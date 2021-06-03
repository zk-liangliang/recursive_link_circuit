pub mod link_recursive_circuit;
pub mod cross_rollup_transaction;

#[cfg(test)]
mod test {

    use franklin_crypto::bellman::pairing::bn256::{Bn256, Fr};
    use franklin_crypto::bellman::pairing::ff::{Field, ScalarEngine};
    use franklin_crypto::bellman::pairing::{CurveAffine, Engine};

    use franklin_crypto::plonk::circuit::verifier_circuit::test::*;
    use franklin_crypto::plonk::circuit::*;

    use franklin_crypto::bellman::plonk::better_cs::cs::Circuit as OldCircuit;
    use franklin_crypto::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;
    use franklin_crypto::bellman::plonk::better_cs::generator::GeneratorAssembly4WithNextStep as OldActualAssembly;
    use franklin_crypto::bellman::plonk::better_cs::verifier::{verify_and_aggregate,verify as old_verify};
    use franklin_crypto::bellman::plonk::better_cs::prover::ProverAssembly4WithNextStep as OldActualProver;
    use franklin_crypto::bellman::plonk::better_cs::keys::{
        Proof, SetupPolynomialsPrecomputations, VerificationKey,
    };

    use franklin_crypto::bellman::kate_commitment::*;
    use franklin_crypto::bellman::plonk::better_better_cs::setup::VerificationKey as NewVerificationKey;
    use franklin_crypto::bellman::plonk::better_better_cs::proof::Proof as NewProof;
    use franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;
    use franklin_crypto::bellman::plonk::better_better_cs::cs::{
        Circuit, TrivialAssembly, Width4MainGateWithDNext,
    };
    use franklin_crypto::bellman::plonk::commitments::transcript::*;
    use franklin_crypto::bellman::plonk::commitments::transcript::Transcript;
    use franklin_crypto::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;

    use franklin_crypto::bellman::plonk::fft::cooley_tukey_ntt::*;
    use franklin_crypto::bellman::worker::*;
    
    use franklin_crypto::rescue::bn256::*;
    use franklin_crypto::rescue::rescue_transcript::RescueTranscriptForRNS;
    use franklin_crypto::plonk::circuit::bigint::field::*;
    use franklin_crypto::plonk::circuit::verifier_circuit::channel::RescueChannelGadget;
    use franklin_crypto::plonk::circuit::verifier_circuit::data_structs::IntoLimbedWitness;
    use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::{
        without_flag_unchecked::*, aux_data::{BN256AuxData,AuxData}
    };
    use super::cross_rollup_transaction::BlockWitness;
    use super::link_recursive_circuit::{
        create_recursive_circuit_vk_and_setup, proof_recursive_aggregate_for_zksync, make_vks_tree,
        RecursiveLinkCircuitBn256, make_public_input_and_limbed_aggregate, make_aggregate,RecursiveLinkCircuit
    };

    #[test]
    fn test_two_proofs() {
        let a = Fr::one();
        let b = Fr::one();

        let num_steps = 40;
        let circuit_0 = BenchmarkCircuit::<Bn256> {
            num_steps,
            a,
            b,
            output: fibbonacci(&a, &b, num_steps),
            _engine_marker: std::marker::PhantomData,
        };

        let num_steps = 18;
        let circuit_1 = BenchmarkCircuit::<Bn256> {
            num_steps,
            a,
            b,
            output: fibbonacci(&a, &b, num_steps),
            _engine_marker: std::marker::PhantomData,
        };

        let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
        let rescue_params = Bn256RescueParams::new_checked_2_into_1();

        let transcript_params = (&rescue_params, &rns_params);

        let (vk_0, proof_0) =
            make_vk_and_proof::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit_0, transcript_params);
        let (vk_1, proof_1) =
            make_vk_and_proof::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit_1, transcript_params);

        let worker = Worker::new();
        let crs_mons = Crs::<Bn256, CrsForMonomialForm>::crs_42(32, &worker);

        let mut g2_bases = [<<Bn256 as Engine>::G2Affine as CurveAffine>::zero(); 2];
        g2_bases.copy_from_slice(&crs_mons.g2_monomial_bases.as_ref()[..]);

        let aux_data = BN256AuxData::new();

        let vks_in_tree = vec![vk_1.clone(), vk_0.clone()];
        // make in reverse
        let (vks_tree, all_witness_values) =
            make_vks_tree(&vks_in_tree, &rescue_params, &rns_params);

        let vks_tree_root = vks_tree.get_commitment();

        let proof_ids = vec![1, 0];

        let mut queries = vec![];
        for idx in 0..2 {
            let proof_id = proof_ids[idx];
            let vk = &vks_in_tree[proof_id];

            let leaf_values = vk
                .into_witness_for_params(&rns_params)
                .expect("must transform into limbed witness");

            let values_per_leaf = leaf_values.len();
            let intra_leaf_indexes_to_query: Vec<_> =
                ((proof_id * values_per_leaf)..((proof_id + 1) * values_per_leaf)).collect();
            let q = vks_tree.produce_query(intra_leaf_indexes_to_query, &all_witness_values);

            assert_eq!(q.values(), &leaf_values[..]);

            queries.push(q.path().to_vec());
        }

        let aggregate = make_aggregate(
            &vec![proof_0.clone(), proof_1.clone()],
            &vec![vk_0.clone(), vk_1.clone()],
            &rescue_params,
            &rns_params
        ).unwrap();

        let (_, _) = make_public_input_and_limbed_aggregate(
            vks_tree_root,
            &proof_ids,
            &vec![proof_0.clone(), proof_1.clone()],
            &aggregate,
            &rns_params
        );

        let recursive_circuit = RecursiveLinkCircuit::<
            Bn256,
            OldActualParams,
            WrapperUnchecked<Bn256>,
            _,
            RescueChannelGadget<Bn256>,
        > {
            num_proofs_to_check: 2,
            num_inputs: 3,
            vk_tree_depth: 1,
            vk_root: Some(vks_tree_root),
            vk_witnesses: Some(vec![vk_0, vk_1]),
            vk_auth_paths: Some(queries),
            proof_ids: Some(proof_ids),
            proofs: Some(vec![proof_0, proof_1]),
            rescue_params: &rescue_params,
            rns_params: &rns_params,
            aux_data,
            transcript_params: &rescue_params,

            chain_id: 0,
            eth_block_witness: BlockWitness::<Bn256>::default(),
            bsc_block_witness: BlockWitness::<Bn256>::default(),
            heco_block_witness: BlockWitness::<Bn256>::default(),
            sol_block_witness: BlockWitness::<Bn256>::default(),
            g2_elements: Some(g2_bases),

            _m: std::marker::PhantomData,
        };

        let mut cs =
            TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        recursive_circuit
            .synthesize(&mut cs)
            .expect("should synthesize");
        println!("Raw number of gates: {}", cs.n());
        cs.finalize();
        println!("Padded number of gates: {}", cs.n());
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_inputs, 1);
    }

    fn make_vk_and_proof<'a, E: Engine, T: Transcript<E::Fr>>(
        circuit: BenchmarkCircuit<E>,
        transcript_params: <T as Prng<E::Fr>>::InitializationParameters,
    ) -> (
        VerificationKey<E, OldActualParams>,
        Proof<E, OldActualParams>,
    ) {
        let worker = Worker::new();
        let mut assembly = OldActualAssembly::<E>::new();
        circuit
            .clone()
            .synthesize(&mut assembly)
            .expect("should synthesize");
        assembly.finalize();
        let setup = assembly.setup(&worker).expect("should setup");

        let crs_mons =
            Crs::<E, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
        let crs_vals =
            Crs::<E, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

        let verification_key =
            VerificationKey::from_setup(&setup, &worker, &crs_mons).expect("should create vk");

        let precomputations = SetupPolynomialsPrecomputations::from_setup(&setup, &worker)
            .expect("should create precomputations");

        let mut prover = OldActualProver::<E>::new();
        circuit.synthesize(&mut prover).expect("should synthesize");
        prover.finalize();

        let size = setup.permutation_polynomials[0].size();

        let omegas_bitreversed =
            BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed =
            <OmegasInvBitreversed<E::Fr> as CTPrecomputations<E::Fr>>::new_for_domain_size(
                size.next_power_of_two(),
            );

        println!("BEFORE PROVE");

        let proof = prover
            .prove::<T, _, _>(
                &worker,
                &setup,
                &precomputations,
                &crs_vals,
                &crs_mons,
                &omegas_bitreversed,
                &omegas_inv_bitreversed,
                Some(transcript_params.clone()),
            )
            .expect("should prove");

        println!("DONE");

        let (is_valid, [_for_gen, _for_x]) =
            verify_and_aggregate::<_, _, T>(&proof, &verification_key, Some(transcript_params))
                .expect("should verify");

        assert!(is_valid);

        println!("PROOF IS VALID");

        (verification_key, proof)
    }

    fn open_crs_for_log2_of_size(n: usize) -> Crs::<Bn256, CrsForMonomialForm> {
        let base_path = std::path::Path::new("/Users/alexvlasov/Downloads/setup/processed");
        let full_path = base_path.join(&format!("setup_2^{}.key", n));
        println!("Opening {}", full_path.to_string_lossy());
        let file = std::fs::File::open(full_path).unwrap();
        let reader = std::io::BufReader::with_capacity(1 << 24, file);

        let crs = Crs::<Bn256, CrsForMonomialForm>::read(reader).unwrap();

        crs
    }

    #[test]
    fn create_vk() {
        let crs = open_crs_for_log2_of_size(22);

        // let size = 1 << 22;
        // let worker = Worker::new();
        // let crs = Crs::<Bn256, CrsForMonomialForm>::crs_42(size, &worker);

        let (vk, _) = create_recursive_circuit_vk_and_setup(2, 1, 3, &crs).unwrap();

        dbg!(vk);
    }

    fn make_vk_and_proof_for_crs<'a, E: Engine, T: Transcript<E::Fr>>(
        circuit: BenchmarkCircuitWithOneInput<E>,
        transcript_params: <T as Prng<E::Fr>>::InitializationParameters,
        crs: &Crs::<E, CrsForMonomialForm>,
    ) -> (
        VerificationKey<E, OldActualParams>,
        Proof<E, OldActualParams>,
    ) {
        let worker = Worker::new();
        let mut assembly = OldActualAssembly::<E>::new();
        circuit
            .synthesize(&mut assembly)
            .expect("should synthesize");
        assembly.finalize();
        let setup = assembly.setup(&worker).expect("should setup");

        let verification_key =
            VerificationKey::from_setup(&setup, &worker, &crs).expect("should create vk");

        let proof = franklin_crypto::bellman::plonk::prove_native_by_steps::<E, _, T>(
            &circuit,
            &setup,
            None,
            crs,
            Some(transcript_params.clone())
        ).expect("should create a proof");

        let (is_valid, [_for_gen, _for_x]) =
            verify_and_aggregate::<_, _, T>(&proof, &verification_key, Some(transcript_params))
                .expect("should verify");

        assert!(is_valid);

        (verification_key, proof)
    }

    #[test]
    fn simulate_zksync_proofs() {
        let a = Fr::one();
        let b = Fr::one();

        let mut circuits = vec![];
        for num_steps in vec![18, 40, 25, 35].into_iter() {
            let circuit = BenchmarkCircuitWithOneInput::<Bn256> {
                num_steps,
                a,
                b,
                output: fibbonacci(&a, &b, num_steps),
                _engine_marker: std::marker::PhantomData,
            };

            circuits.push(circuit);
        }


        let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
        let rescue_params = Bn256RescueParams::new_checked_2_into_1();

        let transcript_params = (&rescue_params, &rns_params);

        let crs = open_crs_for_log2_of_size(24);

        let mut vks = vec![];
        let mut proofs = vec![];

        for circuit in circuits.into_iter() {
            let (vk, proof) =
                make_vk_and_proof_for_crs::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit, transcript_params, &crs);

            let valid = old_verify::<_, _, RescueTranscriptForRNS<Bn256>>(
                &proof,
                &vk,
                Some(transcript_params)
            ).expect("must verify");
            assert!(valid);

            vks.push(vk);
            proofs.push(proof);
        }

        let num_inputs = 1;
        let num_proofs_to_check = 2;
        let tree_depth = 3;

        let (vk_for_recursive_circut, setup) = create_recursive_circuit_vk_and_setup(
            num_proofs_to_check,
            num_inputs,
            tree_depth,
            &crs,
        ).expect("must create recursive circuit verification key");

        let proofs_to_check = vec![2,3];
        let proofs = vec![proofs[2].clone(), proofs[3].clone()];

        let worker = Worker::new();

        let proof = proof_recursive_aggregate_for_zksync(
            tree_depth,
            num_inputs,
            &vks,
            &proofs,
            &proofs_to_check,
            &vk_for_recursive_circut,
            &setup,
            &crs,
            true,
            &worker
        ).expect("must check if satisfied and make a proof");

        let is_valid = verify::<_, _, RollingKeccakTranscript<<Bn256 as ScalarEngine>::Fr>>(
            &vk_for_recursive_circut,
            &proof,
            None,
        ).expect("must perform verification");

        assert!(is_valid);

        let path = std::path::Path::new("./vk.key");
        let file = std::fs::File::create(path).unwrap();
        let mut writer = std::io::BufWriter::with_capacity(1 << 24, file);

        vk_for_recursive_circut.write(&mut writer).expect("must write");

        let path = std::path::Path::new("./proof.proof");
        let file = std::fs::File::create(path).unwrap();
        let mut writer = std::io::BufWriter::with_capacity(1 << 24, file);

        proof.write(&mut writer).expect("must write");

        let mut tmp = vec![];
        vk_for_recursive_circut.write(&mut tmp).expect("must write");

        let vk_deser = NewVerificationKey::<Bn256, RecursiveLinkCircuitBn256>::read(&tmp[..]).expect("must read");

        assert_eq!(vk_for_recursive_circut.permutation_commitments, vk_deser.permutation_commitments);

        let mut tmp = vec![];
        proof.write(&mut tmp).expect("must write");

        let proof_deser = NewProof::<Bn256, RecursiveLinkCircuitBn256>::read(&tmp[..]).expect("must read");

        assert_eq!(proof.quotient_poly_opening_at_z, proof_deser.quotient_poly_opening_at_z);
    }

    #[test]
    fn test_verification_from_binary() {
        let path = std::path::Path::new("./vk.key");
        let file = std::fs::File::open(path).unwrap();
        let reader = std::io::BufReader::with_capacity(1 << 24, file);

        let vk_for_recursive_circut = NewVerificationKey::<Bn256, RecursiveLinkCircuitBn256>::read(reader).expect("must read");

        let path = std::path::Path::new("./proof.proof");
        let file = std::fs::File::open(path).unwrap();
        let reader = std::io::BufReader::with_capacity(1 << 24, file);

        let proof = NewProof::<Bn256, RecursiveLinkCircuitBn256>::read(reader).expect("must read");

        let is_valid = verify::<_, _, RollingKeccakTranscript<<Bn256 as ScalarEngine>::Fr>>(
            &vk_for_recursive_circut,
            &proof,
            None,
        ).expect("must perform verification");

        assert!(is_valid);
    }

    #[test]
    fn simulate_many_proofs() {
        let a = Fr::one();
        let b = Fr::one();

        let mut circuits = vec![];
        for num_steps in vec![18, 40, 25, 35].into_iter() {
            let circuit = BenchmarkCircuitWithOneInput::<Bn256> {
                num_steps,
                a,
                b,
                output: fibbonacci(&a, &b, num_steps),
                _engine_marker: std::marker::PhantomData,
            };

            circuits.push(circuit);
        }


        let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
        let rescue_params = Bn256RescueParams::new_checked_2_into_1();

        let transcript_params = (&rescue_params, &rns_params);

        let crs = open_crs_for_log2_of_size(24);

        let mut vks = vec![];
        let mut proofs = vec![];

        for circuit in circuits.into_iter() {
            let (vk, proof) =
                make_vk_and_proof_for_crs::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit, transcript_params, &crs);

            let valid = old_verify::<_, _, RescueTranscriptForRNS<Bn256>>(
                &proof,
                &vk,
                Some(transcript_params)
            ).expect("must verify");
            assert!(valid);

            vks.push(vk);
            proofs.push(proof);
        }

        let num_inputs = 1;
        let tree_depth = 3;

        let num_proofs_to_check = 2;

        // this is dummy
        println!("Creating setup and verification key");
        let (vk_for_recursive_circut, setup) = create_recursive_circuit_vk_and_setup(
            num_proofs_to_check,
            num_inputs,
            tree_depth,
            &crs,
        ).expect("must create recursive circuit verification key");

        let proofs_indexes_to_check = vec![2,3];
        assert_eq!(proofs_indexes_to_check.len(), num_proofs_to_check);

        let proofs_to_check = vec![proofs[2].clone(), proofs[3].clone()];
        assert_eq!(proofs_to_check.len(), num_proofs_to_check);

        let worker = Worker::new();

        println!("Creating proof");
        let _ = proof_recursive_aggregate_for_zksync(
            tree_depth,
            num_inputs,
            &vks,
            &proofs_to_check,
            &proofs_indexes_to_check,
            &vk_for_recursive_circut,
            &setup,
            &crs,
            true,
            &worker
        ).expect("must check if satisfied and make a proof");
    }
}