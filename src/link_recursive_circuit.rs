#![allow(dead_code)]
use franklin_crypto::bellman::{
    kate_commitment::*,
    pairing::{bn256::Bn256, ff::*, *},
    worker::Worker,
    SynthesisError,
};

use franklin_crypto::bellman::plonk::better_cs::{
    cs::{
        PlonkConstraintSystemParams as OldCSParams,
        PlonkCsWidth4WithNextStepParams as OldActualParams,
    },
    generator::make_non_residues,
    keys::{Proof, VerificationKey},
};
use franklin_crypto::plonk::circuit::{
    allocated_num::*,
    bigint::field::*,
    bigint::range_constraint_gate::TwoBitDecompositionRangecheckCustomGate,
    boolean::*,
    linear_combination::*,
    rescue::*,
    sha256::sha256 as sha256_circuit_hash,
    verifier_circuit::{
        affine_point_wrapper::{
            aux_data::*, without_flag_unchecked::WrapperUnchecked, WrappedAffinePoint,
        },
        channel::*,
        data_structs::*,
        verifying_circuit::aggregate_proof,
    },
    Width4WithCustomGates,
};

use franklin_crypto::bellman::plonk::{
    better_better_cs::{
        cs::*,
        proof::Proof as NewProof,
        setup::{Setup as NewSetup, VerificationKey as NewVerificationKey},
        trees::{binary_tree::*, tree_hash::BinaryTreeHasher},
        verifier::verify,
    },
    commitments::transcript::keccak_transcript::RollingKeccakTranscript,
};

use super::cross_rollup_transaction::{AllocatedBlock, BlockWitness};
use crypto::{digest::Digest, sha2::Sha256};
use franklin_crypto::circuit::Assignment;
use franklin_crypto::rescue::{
    bn256::Bn256RescueParams, rescue_hash as rescue_hash_out_of_circuit, RescueEngine,
    RescueHashParams, StatefulRescue,
};
use once_cell::sync::Lazy;

pub static RNS_PARAMETERS: Lazy<RnsParameters<Bn256, <Bn256 as Engine>::Fq>> =
    Lazy::new(|| RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4));

pub static RESCUE_PARAMETERS: Lazy<Bn256RescueParams> =
    Lazy::new(Bn256RescueParams::new_checked_2_into_1);

pub const ALIGN_FIELD_ELEMENTS_TO_BITS: usize = 256;

#[derive(Clone, Debug)]
pub struct RecursiveLinkCircuit<
    'a,
    E: RescueEngine,
    P: OldCSParams<E>,
    WP: WrappedAffinePoint<'a, E>,
    AD: AuxData<E>,
    T: ChannelGadget<E>,
> {
    pub num_proofs_to_check: usize,
    pub num_inputs: usize,
    pub vk_tree_depth: usize,
    pub vk_root: Option<E::Fr>,
    pub vk_witnesses: Option<Vec<VerificationKey<E, P>>>,
    pub vk_auth_paths: Option<Vec<Vec<E::Fr>>>,
    pub proof_ids: Option<Vec<usize>>,
    pub proofs: Option<Vec<Proof<E, P>>>,
    pub rescue_params: &'a E::Params,
    pub rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    pub aux_data: AD,
    pub transcript_params: &'a T::Params,

    pub chain_id: u32,
    pub eth_block_witness: BlockWitness<E>,
    pub bsc_block_witness: BlockWitness<E>,
    pub heco_block_witness: BlockWitness<E>,
    pub sol_block_witness: BlockWitness<E>,

    pub g2_elements: Option<[E::G2Affine; 2]>,

    pub _m: std::marker::PhantomData<WP>,
}

impl<
        'a,
        E: RescueEngine,
        P: OldCSParams<E>,
        WP: WrappedAffinePoint<'a, E>,
        AD: AuxData<E>,
        T: ChannelGadget<E>,
    > Circuit<E> for RecursiveLinkCircuit<'a, E, P, WP, AD, T>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    type MainGate = Width4MainGateWithDNext;

    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let num_bits_in_proof_id = self.vk_tree_depth;
        let non_residues = make_non_residues::<E::Fr>(P::STATE_WIDTH - 1);

        if let Some(proofs) = self.proofs.as_ref() {
            assert_eq!(self.num_proofs_to_check, proofs.len());
        }
        if let Some(proof_ids) = self.proof_ids.as_ref() {
            assert_eq!(self.num_proofs_to_check, proof_ids.len());
        }
        if let Some(vk_witnesses) = self.vk_witnesses.as_ref() {
            assert_eq!(self.num_proofs_to_check, vk_witnesses.len());
        }
        if let Some(vk_auth_paths) = self.vk_auth_paths.as_ref() {
            assert_eq!(self.num_proofs_to_check, vk_auth_paths.len());
        }

        // Allocate everything, get fs scalar for aggregation
        let mut proof_witnesses = vec![];
        let mut fs_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let proof_witness = self.proofs.as_ref().map(|el| el[proof_index].clone());

            if let Some(proof) = proof_witness.as_ref() {
                assert_eq!(
                    proof.input_values.len(),
                    self.num_inputs,
                    "proof has too many inputs"
                );
                // assert!(proof.input_values.len() <= self.num_inputs, "proof has too many inputs");
            }

            let allocated_proof = ProofGadget::<E, WP>::alloc_from_witness(
                cs,
                self.num_inputs,
                &proof_witness,
                self.rns_params,
                &self.aux_data,
            )?;

            let as_num_witness = allocated_proof.into_witness(cs)?;

            fs_witnesses.extend(as_num_witness);
            proof_witnesses.push(allocated_proof);
        }

        let mut vk_witnesses = vec![];
        let mut vk_leaf_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let vk_witness = self.vk_witnesses.as_ref().map(|el| {
                el[proof_index]
                    .into_witness_for_params(self.rns_params)
                    .expect("must transform into limbed witness")
            });

            let expected_witness_size =
                VerificationKey::<E, P>::witness_size_for_params(self.rns_params);

            if let Some(vk_witness) = vk_witness.as_ref() {
                assert_eq!(
                    vk_witness.len(),
                    expected_witness_size,
                    "witness size is not sufficient to create verification key"
                );
            }

            let mut allocated = vec![];
            for idx in 0..expected_witness_size {
                let wit = vk_witness.as_ref().map(|el| el[idx]);
                let num = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

                allocated.push(num);
            }

            let domain_size = &allocated[0];
            let omega = &allocated[1];
            let key = &allocated[2..];

            let allocated_vk = VerificationKeyGagdet::<E, WP>::alloc_from_limbs_witness::<_, P, AD>(
                cs,
                self.num_inputs,
                domain_size,
                omega,
                key,
                self.rns_params,
                non_residues.clone(),
                &self.aux_data,
            )?;
            vk_witnesses.push(allocated_vk);
            vk_leaf_witnesses.push(allocated);
        }

        // proofs and verification keys are allocated, not proceed with aggregation

        // first get that FS scalar
        let mut sponge = StatefulRescueGadget::<E>::new(self.rescue_params);

        for w in fs_witnesses.into_iter() {
            sponge.absorb_single_value(cs, w, self.rescue_params)?;
        }
        sponge.pad_if_necessary(self.rescue_params)?;

        let aggregation_challenge = sponge
            .squeeze_out_single(cs, self.rescue_params)?
            .into_allocated_num(cs)?;

        // then perform individual aggregation
        let mut pairs_for_generator = vec![];
        let mut pairs_for_x = vec![];

        for proof_idx in 0..self.num_proofs_to_check {
            let proof = &proof_witnesses[proof_idx];
            let vk = &vk_witnesses[proof_idx];
            let [pair_with_generator, pair_with_x] = aggregate_proof::<_, _, T, CS::Params, P, _, _>(
                cs,
                self.transcript_params,
                &proof.input_values,
                &vk,
                &proof,
                &self.aux_data,
                self.rns_params,
            )?;

            pairs_for_generator.push(pair_with_generator);
            pairs_for_x.push(pair_with_x);
        }

        // now make scalars for separation

        let mut scalars = vec![aggregation_challenge];

        let mut current = aggregation_challenge;
        for _ in 1..self.num_proofs_to_check {
            let new = current.mul(cs, &aggregation_challenge)?;
            scalars.push(new);
            current = new;
        }

        // perform final aggregation

        let pair_with_generator = WP::multiexp(
            cs,
            &scalars,
            &pairs_for_generator,
            None,
            self.rns_params,
            &self.aux_data,
        )?;
        let pair_with_x = WP::multiexp(
            cs,
            &scalars,
            &pairs_for_x,
            None,
            self.rns_params,
            &self.aux_data,
        )?;

        if let (Some(with_gen), Some(with_x), Some(g2_elements)) = (
            pair_with_generator.get_point().get_value(),
            pair_with_x.get_point().get_value(),
            self.g2_elements,
        ) {
            let valid = E::final_exponentiation(&E::miller_loop(&[
                (&with_gen.prepare(), &g2_elements[0].prepare()),
                (&with_x.prepare(), &g2_elements[1].prepare()),
            ]))
            .unwrap()
                == E::Fqk::one();

            dbg!(valid);
        }

        // allocate vk ids
        let mut key_ids = vec![];
        let vk_root = AllocatedNum::alloc(cs, || Ok(*self.vk_root.get()?))?;

        {
            // compute vk_root constraints
            for proof_index in 0..self.num_proofs_to_check {
                let vk_witness = &vk_leaf_witnesses[proof_index];
                let path_witness = self
                    .proof_ids
                    .as_ref()
                    .map(|el| E::Fr::from_str(&el[proof_index].to_string()).unwrap());
                let path_allocated = AllocatedNum::alloc(cs, || Ok(*path_witness.get()?))?;

                let path_bits = path_allocated.into_bits_le(cs, Some(num_bits_in_proof_id))?;

                key_ids.push(path_bits.clone());

                let mut auth_path = vec![];
                for path_idx in 0..self.vk_tree_depth {
                    let auth_witness = self
                        .vk_auth_paths
                        .as_ref()
                        .map(|el| el[proof_index][path_idx]);
                    let auth_allocated = AllocatedNum::alloc(cs, || Ok(*auth_witness.get()?))?;

                    auth_path.push(auth_allocated);
                }

                assert_eq!(auth_path.len(), path_bits.len());

                let leaf_hash = rescue_leaf_hash(cs, vk_witness, self.rescue_params)?;
                let mut current = leaf_hash;

                for (path_bit, auth_path) in path_bits.into_iter().zip(auth_path.into_iter()) {
                    let left =
                        AllocatedNum::conditionally_select(cs, &auth_path, &current, &path_bit)?;
                    let right =
                        AllocatedNum::conditionally_select(cs, &current, &auth_path, &path_bit)?;
                    let node_hash = rescue_node_hash(cs, left, right, self.rescue_params)?;

                    current = node_hash;
                }
                current.enforce_equal(cs, &vk_root)?;
            }
        }

        // VKs tree
        let mut hash_to_public_inputs = vec![];
        hash_to_public_inputs.extend(allocated_num_to_aligned_big_endian(cs, &vk_root)?);

        // first aggregate proof ids into u8
        for mut proof in key_ids.into_iter().take(self.num_proofs_to_check) {
            assert!(proof.len() < 8);

            proof.resize(8, Boolean::constant(false));
            proof.reverse();

            hash_to_public_inputs.extend(proof);
        }

        // now aggregate original public inputs
        let bsc_block = AllocatedBlock::from_witness(cs, &self.bsc_block_witness, 0u8)?;
        let eth_block = AllocatedBlock::from_witness(cs, &self.eth_block_witness, 1u8)?;
        let heco_block = AllocatedBlock::from_witness(cs, &self.heco_block_witness, 2u8)?;
        let sol_block = AllocatedBlock::from_witness(cs, &self.sol_block_witness, 3u8)?;

        for (proof_idx, allocated_proof) in proof_witnesses
            .iter()
            .enumerate()
            .take(self.num_proofs_to_check)
        {
            for input_idx in 0..self.num_inputs {
                let input = &allocated_proof.input_values[input_idx];
                let serialized = allocated_num_to_aligned_big_endian(cs, input)?;
                match proof_idx {
                    0 => input.enforce_equal(cs, &bsc_block.block_commitment)?,
                    1 => input.enforce_equal(cs, &eth_block.block_commitment)?,
                    2 => input.enforce_equal(cs, &heco_block.block_commitment)?,
                    3 => input.enforce_equal(cs, &sol_block.block_commitment)?,
                    _ => return Err(SynthesisError::Unsatisfiable),
                };
                hash_to_public_inputs.extend(serialized);
            }
        }
        // deal cross rollup constraints
        bsc_block
            .cross_eth_txs_commitment
            .enforce_equal(cs, &eth_block.cross_bsc_txs_commitment)?;
        bsc_block
            .cross_heco_txs_commitment
            .enforce_equal(cs, &heco_block.cross_bsc_txs_commitment)?;
        bsc_block
            .cross_sol_txs_commitment
            .enforce_equal(cs, &sol_block.cross_bsc_txs_commitment)?;

        eth_block
            .cross_heco_txs_commitment
            .enforce_equal(cs, &heco_block.cross_eth_txs_commitment)?;
        eth_block
            .cross_sol_txs_commitment
            .enforce_equal(cs, &sol_block.cross_eth_txs_commitment)?;

        heco_block
            .cross_sol_txs_commitment
            .enforce_equal(cs, &sol_block.cross_heco_txs_commitment)?;

        // now serialize field elements as limbs
        hash_to_public_inputs.extend(serialize_point_into_big_endian(cs, &pair_with_generator)?);
        hash_to_public_inputs.extend(serialize_point_into_big_endian(cs, &pair_with_x)?);

        let input_commitment = sha256_circuit_hash(cs, &hash_to_public_inputs)?;
        let as_num = aligned_big_endian_to_allocated_num(cs, input_commitment)?;
        as_num.inputize(cs)?;

        Ok(())
    }

    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(vec![
            Self::MainGate::default().into_internal(),
            TwoBitDecompositionRangecheckCustomGate::default().into_internal(),
        ])
    }
}

pub fn aligned_big_endian_to_allocated_num<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bits: Vec<Boolean>,
) -> Result<AllocatedNum<E>, SynthesisError> {
    let keep = bytes_to_keep::<E>();
    assert!(keep <= 32);

    // we don't need to reverse again
    let mut lc = LinearCombination::<E>::zero();
    let mut coeff = E::Fr::one();

    for b in bits[(32 - keep) * 8..].iter().rev() {
        lc.add_assign_boolean_with_coeff(b, coeff);
        coeff.double();
    }

    let as_num = lc.into_allocated_num(cs)?;

    Ok(as_num)
}
pub fn allocated_num_to_aligned_big_endian<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = el.into_bits_le(cs, None)?;

    assert!(bits.len() < ALIGN_FIELD_ELEMENTS_TO_BITS);

    bits.resize(ALIGN_FIELD_ELEMENTS_TO_BITS, Boolean::constant(false));

    bits.reverse();

    Ok(bits)
}

fn debug_print_boolean_array_as_hex(input: &[Boolean]) {
    assert_eq!(input.len() % 8, 0);

    let mut result = vec![];

    for byte in input.chunks(8) {
        let mut byte_value = 0u8;
        for (idx, bit) in byte.iter().enumerate() {
            if let Some(value) = bit.get_value() {
                let base = if value { 1u8 } else { 0u8 };

                byte_value += base << (7 - idx);
            } else {
                return;
            }
        }

        result.push(byte_value);
    }

    println!("Value = {}", hex::encode(&result));
}

fn allocated_num_to_big_endian_of_fixed_width<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
    limit: usize,
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = el.into_bits_le(cs, Some(limit))?;
    bits.reverse();

    Ok(bits)
}

fn serialize_point_into_big_endian<
    'a,
    E: Engine,
    CS: ConstraintSystem<E>,
    WP: WrappedAffinePoint<'a, E>,
>(
    cs: &mut CS,
    point: &WP,
) -> Result<Vec<Boolean>, SynthesisError> {
    let raw_point = point.get_point();

    let x = raw_point
        .get_x()
        .force_reduce_into_field(cs)?
        .enforce_is_normalized(cs)?;
    let y = raw_point
        .get_y()
        .force_reduce_into_field(cs)?
        .enforce_is_normalized(cs)?;

    let mut serialized = vec![];

    for coord in vec![x, y].into_iter() {
        for limb in coord.into_limbs().into_iter() {
            let as_num = limb.into_variable(); // this checks coeff and constant term internally
            serialized.extend(allocated_num_to_aligned_big_endian(cs, &as_num)?);
        }
    }

    Ok(serialized)
}

fn rescue_leaf_hash<E: RescueEngine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    leaf: &[AllocatedNum<E>],
    params: &E::Params,
) -> Result<AllocatedNum<E>, SynthesisError>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    let mut rescue_gadget = StatefulRescueGadget::<E>::new(&params);

    rescue_gadget.specizalize(leaf.len() as u8);
    rescue_gadget.absorb(cs, leaf, params)?;

    let output = rescue_gadget.squeeze_out_single(cs, params)?;

    let as_num = output.into_allocated_num(cs)?;

    Ok(as_num)
}

fn rescue_node_hash<E: RescueEngine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    left: AllocatedNum<E>,
    right: AllocatedNum<E>,
    params: &E::Params,
) -> Result<AllocatedNum<E>, SynthesisError>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    let mut rescue_gadget = StatefulRescueGadget::<E>::new(&params);

    rescue_gadget.specizalize(2);
    rescue_gadget.absorb(cs, &[left, right], params)?;

    let output = rescue_gadget.squeeze_out_single(cs, params)?;

    let as_num = output.into_allocated_num(cs)?;

    Ok(as_num)
}

pub struct StaticRescueBinaryTreeHasher<E: RescueEngine> {
    params: E::Params,
}

impl<E: RescueEngine> StaticRescueBinaryTreeHasher<E> {
    pub fn new(params: &E::Params) -> Self {
        assert_eq!(params.rate(), 2u32);
        assert_eq!(params.output_len(), 1u32);
        Self {
            params: params.clone(),
        }
    }
}

impl<E: RescueEngine> Clone for StaticRescueBinaryTreeHasher<E> {
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }
}

impl<E: RescueEngine> BinaryTreeHasher<E::Fr> for StaticRescueBinaryTreeHasher<E> {
    type Output = E::Fr;

    #[inline]
    fn placeholder_output() -> Self::Output {
        E::Fr::zero()
    }

    fn leaf_hash(&self, input: &[E::Fr]) -> Self::Output {
        let mut as_vec = rescue_hash_out_of_circuit::<E>(&self.params, input);

        as_vec.pop().unwrap()
    }

    fn node_hash(&self, input: &[Self::Output; 2], _level: usize) -> Self::Output {
        let mut as_vec = rescue_hash_out_of_circuit::<E>(&self.params, &input[..]);

        as_vec.pop().unwrap()
    }
}

pub fn make_vks_tree<'a, E: RescueEngine, P: OldCSParams<E>>(
    vks: &[VerificationKey<E, P>],
    params: &'a E::Params,
    rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> (BinaryTree<E, StaticRescueBinaryTreeHasher<E>>, Vec<E::Fr>) {
    let mut leaf_combinations: Vec<Vec<&[E::Fr]>> = vec![vec![]; vks.len()];

    let hasher = StaticRescueBinaryTreeHasher::new(params);
    let mut tmp = vec![];

    for vk in vks.iter() {
        let witness = vk
            .into_witness_for_params(rns_params)
            .expect("must transform into limbed witness");
        tmp.push(witness);
    }

    for idx in 0..vks.len() {
        leaf_combinations[idx].push(&tmp[idx][..]);
    }

    let tree_params = BinaryTreeParams {
        values_per_leaf: VerificationKey::<E, P>::witness_size_for_params(rns_params),
    };

    let tree = BinaryTree::<E, _>::create_from_combined_leafs(
        &leaf_combinations[..],
        1,
        hasher,
        &tree_params,
    );

    let mut all_values = vec![];
    for w in tmp.into_iter() {
        all_values.extend(w);
    }

    (tree, all_values)
}

pub fn make_aggregate<'a, E: RescueEngine, P: OldCSParams<E>>(
    proofs: &[Proof<E, P>],
    vks: &[VerificationKey<E, P>],
    params: &'a E::Params,
    rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> Result<[E::G1Affine; 2], SynthesisError> {
    use franklin_crypto::bellman::plonk::better_cs::verifier::verify_and_aggregate;
    use franklin_crypto::rescue::rescue_transcript::RescueTranscriptForRNS;

    assert_eq!(
        proofs.len(),
        vks.len(),
        "number of proofs is not equal to number of VKs"
    );

    let mut channel = StatefulRescue::<E>::new(params);
    for p in proofs.iter() {
        let as_fe = p.into_witness_for_params(rns_params)?;

        for fe in as_fe.into_iter() {
            channel.absorb_single_value(fe);
        }
    }

    channel.pad_if_necessary();

    let aggregation_challenge: E::Fr = channel.squeeze_out_single();

    let mut pair_with_generator = E::G1::zero();
    let mut pair_with_x = E::G1::zero();

    let mut current = aggregation_challenge;

    for (vk, proof) in vks.iter().zip(proofs.iter()) {
        let (is_valid, [for_gen, for_x]) = verify_and_aggregate::<_, _, RescueTranscriptForRNS<E>>(
            &proof,
            &vk,
            Some((params, rns_params)),
        )
        .expect("should verify");

        assert!(is_valid, "individual proof is not valid");

        let contribution = for_gen.mul(current.into_repr());
        pair_with_generator.add_assign(&contribution);

        let contribution = for_x.mul(current.into_repr());
        pair_with_x.add_assign(&contribution);

        current.mul_assign(&aggregation_challenge);
    }

    let pair_with_generator = pair_with_generator.into_affine();
    let pair_with_x = pair_with_x.into_affine();

    assert!(!pair_with_generator.is_zero());
    assert!(!pair_with_x.is_zero());

    Ok([pair_with_generator, pair_with_x])
}

pub fn make_public_input_and_limbed_aggregate<E: Engine, P: OldCSParams<E>>(
    vks_root: E::Fr,
    proof_indexes: &[usize],
    proofs: &[Proof<E, P>],
    aggregate: &[E::G1Affine; 2],
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> (E::Fr, Vec<E::Fr>) {
    let (input, limbed_aggregate) = make_public_input_for_hashing_and_limbed_aggreagated(
        vks_root,
        proof_indexes,
        proofs,
        aggregate,
        rns_params,
    );

    let mut h = Sha256::new();
    h.input(&input);
    let mut hash_output = [0u8; 32];
    h.result(&mut hash_output[..]);

    let keep = bytes_to_keep::<E>();
    hash_output
        .iter_mut()
        .take(32 - keep)
        .for_each(|hash_u8| *hash_u8 = 0);

    let mut repr = <E::Fr as PrimeField>::Repr::default();
    repr.read_be(&hash_output[..]).expect("must read BE repr");

    let fe = E::Fr::from_repr(repr).expect("must be valid representation");

    (fe, limbed_aggregate)
}

fn make_public_input_for_hashing_and_limbed_aggreagated<E: Engine, P: OldCSParams<E>>(
    vks_root: E::Fr,
    proof_indexes: &[usize],
    proofs: &[Proof<E, P>],
    aggregate: &[E::G1Affine; 2],
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> (Vec<u8>, Vec<E::Fr>) {
    let mut result = vec![];

    add_field_element(&vks_root, &mut result);
    for idx in proof_indexes.iter() {
        assert!(*idx < 256);
        result.push(*idx as u8);
    }

    for proof in proofs.iter() {
        for input in proof.input_values.iter() {
            add_field_element(input, &mut result);
        }
    }

    add_point(&aggregate[0], &mut result, rns_params);
    add_point(&aggregate[1], &mut result, rns_params);

    let mut limbed_aggreagate = vec![];
    decompose_point_into_limbs(&aggregate[0], &mut limbed_aggreagate, rns_params);
    decompose_point_into_limbs(&aggregate[1], &mut limbed_aggreagate, rns_params);

    (result, limbed_aggreagate)
}

fn bytes_to_keep<E: Engine>() -> usize {
    (E::Fr::CAPACITY / 8) as usize
}

fn add_field_element<F: PrimeField>(src: &F, dst: &mut Vec<u8>) {
    let repr = src.into_repr();

    let mut buffer = [0u8; 32];
    repr.write_be(&mut buffer[..]).expect("must write");

    dst.extend_from_slice(&buffer);
}

fn add_point<E: Engine>(
    src: &E::G1Affine,
    dst: &mut Vec<u8>,
    params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) {
    let mut tmp_dest = vec![];
    decompose_point_into_limbs(src, &mut tmp_dest, params);

    for p in tmp_dest.into_iter() {
        add_field_element(&p, dst);
    }
}

fn decompose_point_into_limbs<E: Engine>(
    src: &E::G1Affine,
    dst: &mut Vec<E::Fr>,
    params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) {
    use franklin_crypto::plonk::circuit::verifier_circuit::utils::add_point;

    let mut new_params = params.clone();
    new_params.set_prefer_single_limb_allocation(true);

    let params = &new_params;

    add_point(src, dst, &params);
}

pub type RecursiveLinkCircuitBn256<'a> = RecursiveLinkCircuit<
    'a,
    Bn256,
    OldActualParams,
    WrapperUnchecked<'a, Bn256>,
    BN256AuxData,
    RescueChannelGadget<Bn256>,
>;

pub fn create_recursive_circuit_setup<'a>(
    num_proofs_to_check: usize,
    num_inputs: usize,
    vk_tree_depth: usize,
    // bsc_block_witness: BlockWitness<Bn256>,
    // eth_block_witness: BlockWitness<Bn256>,
    // heco_block_witness: BlockWitness<Bn256>,
    // sol_block_witness: BlockWitness<Bn256>,
) -> Result<NewSetup<Bn256, RecursiveLinkCircuitBn256<'a>>, SynthesisError> {
    let mut assembly =
        SetupAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
    let rescue_params = Bn256RescueParams::new_checked_2_into_1();
    let aux_data = BN256AuxData::new();

    // let transcript_params = (&rescue_params, &rns_params);

    let recursive_circuit = RecursiveLinkCircuitBn256 {
        num_proofs_to_check,
        num_inputs,
        vk_tree_depth,
        vk_root: None,

        vk_witnesses: None,
        vk_auth_paths: None,
        proof_ids: None,
        proofs: None,
        rescue_params: &rescue_params,
        rns_params: &rns_params,
        aux_data,
        transcript_params: &rescue_params,

        chain_id: 0,
        bsc_block_witness: BlockWitness::<Bn256>::default(),
        eth_block_witness: BlockWitness::<Bn256>::default(),
        heco_block_witness: BlockWitness::<Bn256>::default(),
        sol_block_witness: BlockWitness::<Bn256>::default(),

        g2_elements: None,

        _m: std::marker::PhantomData,
    };

    recursive_circuit.synthesize(&mut assembly)?;

    let worker = Worker::new();

    assembly.finalize();
    let setup = assembly.create_setup(&worker)?;

    Ok(setup)
}

type NewVerificationKeyAndSetup<'a, E, C> = (NewVerificationKey<E, C>, NewSetup<E, C>);

pub fn create_recursive_circuit_vk_and_setup<'a>(
    num_proofs_to_check: usize,
    num_inputs: usize,
    vk_tree_depth: usize,
    crs: &Crs<Bn256, CrsForMonomialForm>,
) -> Result<NewVerificationKeyAndSetup<Bn256, RecursiveLinkCircuitBn256<'a>>, SynthesisError> {
    let worker = Worker::new();

    let setup = create_recursive_circuit_setup(num_proofs_to_check, num_inputs, vk_tree_depth)?;

    let vk = NewVerificationKey::<Bn256, RecursiveLinkCircuitBn256<'a>>::from_setup(
        &setup, &worker, &crs,
    )?;

    Ok((vk, setup))
}

type TreeAndWitness<E, H> = (BinaryTree<E, H>, Vec<<E as ScalarEngine>::Fr>);
pub fn create_vks_tree(
    vks: &[VerificationKey<Bn256, OldActualParams>],
    tree_depth: usize,
) -> Result<
    (
        usize,
        TreeAndWitness<Bn256, StaticRescueBinaryTreeHasher<Bn256>>,
    ),
    SynthesisError,
> {
    assert!(!vks.is_empty());
    let max_size = 1 << tree_depth;
    assert!(vks.len() <= max_size);

    let max_valid_idx = vks.len() - 1;

    let mut padded = vks.to_vec();
    padded.resize(max_size, vks.last().unwrap().clone());

    let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
    let rescue_params = Bn256RescueParams::new_checked_2_into_1();

    let (tree, witness) = make_vks_tree(&padded, &rescue_params, &rns_params);

    Ok((max_valid_idx, (tree, witness)))
}

pub struct RecursiveAggreagationEthereumDataStorage<E: Engine> {
    pub indexes_of_used_proofs: Vec<u8>,
    pub num_inputs: usize,
    pub individual_proofs_inputs: Vec<Vec<E::Fr>>,
    pub tree_root: E::Fr,
    pub expected_recursive_input: E::Fr,
    pub limbed_aggregated_g1_elements: Vec<E::Fr>,
}

pub const ZKSYNC_NUM_INPUTS: usize = 1;

pub fn create_zksync_recursive_aggregate(
    tree_depth: usize,
    num_inputs: usize,
    all_known_vks: &[VerificationKey<Bn256, OldActualParams>],
    proofs: &[Proof<Bn256, OldActualParams>],
    vk_indexes: &[usize],
    g2_elements: &[<Bn256 as Engine>::G2Affine; 2],
) -> Result<RecursiveAggreagationEthereumDataStorage<Bn256>, SynthesisError> {
    assert_eq!(num_inputs, ZKSYNC_NUM_INPUTS, "invalid number of inputs");

    let rns_params = &*RNS_PARAMETERS;
    let rescue_params = &*RESCUE_PARAMETERS;

    assert!(tree_depth <= 8, "tree must not be deeper than 8");
    let (max_index, (vks_tree, _)) = create_vks_tree(&all_known_vks, tree_depth)?;

    let mut vks_to_aggregate = vec![];
    let mut short_indexes = vec![];
    let mut individual_proofs_inputs = vec![];
    for &index in vk_indexes.iter() {
        assert!(index <= max_index);
        assert!(
            index < 256,
            "for now tree should not be larger than 256 elements"
        );
        let vk = &all_known_vks[index];
        vks_to_aggregate.push(vk.clone());
        short_indexes.push(index as u8);
    }

    for proof in proofs.iter() {
        individual_proofs_inputs.push(proof.input_values.clone());
    }

    let aggregate = make_aggregate(&proofs, &vks_to_aggregate, &rescue_params, &rns_params)?;

    let valid = Bn256::final_exponentiation(&Bn256::miller_loop(&[
        (&aggregate[0].prepare(), &g2_elements[0].prepare()),
        (&aggregate[1].prepare(), &g2_elements[1].prepare()),
    ]))
    .ok_or(SynthesisError::Unsatisfiable)?
        == <Bn256 as Engine>::Fqk::one();

    if !valid {
        println!("Recursive aggreagete is invalid");
        return Err(SynthesisError::Unsatisfiable);
    }

    let vks_tree_root = vks_tree.get_commitment();

    let (expected_input, limbed_aggreagate) = make_public_input_and_limbed_aggregate(
        vks_tree_root,
        &vk_indexes,
        &proofs,
        &aggregate,
        &rns_params,
    );

    let new = RecursiveAggreagationEthereumDataStorage::<Bn256> {
        indexes_of_used_proofs: short_indexes,
        num_inputs: ZKSYNC_NUM_INPUTS,
        individual_proofs_inputs,
        tree_root: vks_tree_root,
        expected_recursive_input: expected_input,
        limbed_aggregated_g1_elements: limbed_aggreagate,
    };

    Ok(new)
}

/// Internally uses RollingKeccakTranscript for Ethereum
#[allow(clippy::too_many_arguments)]
pub fn proof_recursive_aggregate_for_zksync<'a>(
    tree_depth: usize,
    num_inputs: usize,
    all_known_vks: &[VerificationKey<Bn256, OldActualParams>],
    proofs: &[Proof<Bn256, OldActualParams>],
    vk_indexes: &[usize],
    recursive_circuit_vk: &NewVerificationKey<Bn256, RecursiveLinkCircuitBn256<'a>>,
    recursive_circuit_setup: &NewSetup<Bn256, RecursiveLinkCircuitBn256<'a>>,
    crs: &Crs<Bn256, CrsForMonomialForm>,
    quick_check_if_satisifed: bool,
    worker: &Worker,
    // bsc_block_witness: BlockWitness<Bn256>,
    // eth_block_witness: BlockWitness<Bn256>,
    // heco_block_witness: BlockWitness<Bn256>,
    // sol_block_witness: BlockWitness<Bn256>,
) -> Result<NewProof<Bn256, RecursiveLinkCircuitBn256<'a>>, SynthesisError> {
    let rns_params = &*RNS_PARAMETERS;
    let rescue_params = &*RESCUE_PARAMETERS;

    let num_proofs_to_check = proofs.len();

    assert!(tree_depth <= 8, "tree must not be deeper than 8");
    let (max_index, (vks_tree, tree_witnesses)) = create_vks_tree(&all_known_vks, tree_depth)?;

    let mut short_indexes = vec![];
    // let mut individual_proofs_inputs = vec![];
    for &index in vk_indexes.iter() {
        assert!(index <= max_index);
        assert!(
            index < 256,
            "for now tree should not be larger than 256 elements"
        );
        // let vk = &all_known_vks[index];
        // vks_to_aggregate.push(vk.clone());
        short_indexes.push(index as u8);
    }

    let mut queries = vec![];

    let proofs_to_aggregate = proofs;
    let mut vks_to_aggregate = vec![];
    for &proof_id in vk_indexes.iter() {
        let vk = &all_known_vks[proof_id];
        vks_to_aggregate.push(vk.clone());

        let leaf_values = vk
            .into_witness_for_params(&rns_params)
            .expect("must transform into limbed witness");

        let values_per_leaf = leaf_values.len();
        let intra_leaf_indexes_to_query: Vec<_> =
            ((proof_id * values_per_leaf)..((proof_id + 1) * values_per_leaf)).collect();
        let q = vks_tree.produce_query(intra_leaf_indexes_to_query, &tree_witnesses);

        assert_eq!(q.values(), &leaf_values[..]);

        queries.push(q.path().to_vec());
    }

    let aggregate = make_aggregate(
        &proofs_to_aggregate,
        &vks_to_aggregate,
        &rescue_params,
        &rns_params,
    )?;

    let vks_tree_root = vks_tree.get_commitment();

    println!("Assembling input to recursive circuit");

    let (expected_input, _) = make_public_input_and_limbed_aggregate(
        vks_tree_root,
        &vk_indexes,
        &proofs,
        &aggregate,
        &rns_params,
    );

    assert_eq!(recursive_circuit_setup.num_inputs, 1);

    assert_eq!(recursive_circuit_vk.total_lookup_entries_length, 0);

    let mut g2_bases = [<<Bn256 as Engine>::G2Affine as CurveAffine>::zero(); 2];
    g2_bases.copy_from_slice(&crs.g2_monomial_bases.as_ref()[..]);

    let aux_data = BN256AuxData::new();

    let recursive_circuit_with_witness = RecursiveLinkCircuitBn256 {
        num_proofs_to_check,
        num_inputs,
        vk_tree_depth: tree_depth,
        vk_root: Some(vks_tree_root),
        vk_witnesses: Some(vks_to_aggregate),
        vk_auth_paths: Some(queries),
        proof_ids: Some(vk_indexes.to_vec()),
        proofs: Some(proofs_to_aggregate.to_vec()),
        rescue_params: &rescue_params,
        rns_params: &rns_params,
        aux_data,
        transcript_params: &rescue_params,

        chain_id: 0,
        bsc_block_witness: BlockWitness::<Bn256>::default(),
        eth_block_witness: BlockWitness::<Bn256>::default(),
        heco_block_witness: BlockWitness::<Bn256>::default(),
        sol_block_witness: BlockWitness::<Bn256>::default(),

        g2_elements: Some(g2_bases),

        _m: std::marker::PhantomData,
    };

    if quick_check_if_satisifed {
        println!("Checking if satisfied");
        let mut assembly =
            TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        recursive_circuit_with_witness
            .synthesize(&mut assembly)
            .expect("must synthesize");
        println!(
            "Using {} gates for {} proofs aggregated",
            assembly.n(),
            num_proofs_to_check
        );
        let is_satisfied = assembly.is_satisfied();
        println!("Is satisfied = {}", is_satisfied);

        if !is_satisfied {
            return Err(SynthesisError::Unsatisfiable);
        }
    }

    let mut assembly =
        ProvingAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
    recursive_circuit_with_witness
        .synthesize(&mut assembly)
        .expect("must synthesize");
    assembly.finalize();

    let proof = assembly.create_proof::<_, RollingKeccakTranscript<<Bn256 as ScalarEngine>::Fr>>(
        &worker,
        &recursive_circuit_setup,
        &crs,
        None,
    )?;

    assert_eq!(
        proof.inputs[0], expected_input,
        "expected input is not equal to one in a circuit"
    );

    let is_valid = verify::<_, _, RollingKeccakTranscript<<Bn256 as ScalarEngine>::Fr>>(
        &recursive_circuit_vk,
        &proof,
        None,
    )?;

    if !is_valid {
        println!("Recursive circuit proof is invalid");
        return Err(SynthesisError::Unsatisfiable);
    }

    Ok(proof)
}
