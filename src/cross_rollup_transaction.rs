use super::link_recursive_circuit::{
    aligned_big_endian_to_allocated_num, allocated_num_to_aligned_big_endian,
};
use crypto::{digest::Digest, sha2::Sha256};
use franklin_crypto::plonk::circuit::{
    allocated_num::AllocatedNum, sha256::sha256 as sha256_circuit_hash,
};
use franklin_crypto::{
    bellman::plonk::better_better_cs::cs::ConstraintSystem,
    bellman::{BitIterator, Field, PrimeField, PrimeFieldRepr, SynthesisError},
    rescue::RescueEngine,
};

pub struct AllocatedBlock<E: RescueEngine> {
    // block_number + validator_address
    // old_root
    // new_root
    // block_timestamp
    // public_data_commitment + op_offset_commitment
    pub rolling_commitment: AllocatedNum<E>,
    pub block_commitment: AllocatedNum<E>,
    pub chain_id: u8,

    pub cross_bsc_txs_commitment: AllocatedNum<E>,
    pub cross_eth_txs_commitment: AllocatedNum<E>,
    pub cross_heco_txs_commitment: AllocatedNum<E>,
    pub cross_sol_txs_commitment: AllocatedNum<E>,
}

impl<E: RescueEngine> AllocatedBlock<E> {
    pub fn from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        block: &BlockWitness<E>,
        chain_id: u8,
    ) -> Result<AllocatedBlock<E>, SynthesisError> {
        let rolling_commitment = public_data_commitment::<E>(
            E::Fr::one(),
            &block.public_data_commitment,
            block.old_root,
            block.new_root,
            block.validator_address,
            block.block_number,
            block.block_timestamp,
            &block.op_offset_commitment,
        );

        let mut rolling_hash: Vec<bool> =
            BitIterator::new(rolling_commitment.into_repr()).collect();
        let cross_bsc_tx_hash: Vec<bool> =
            BitIterator::new(block.cross_bsc_txs_commitment.into_repr()).collect();
        let cross_eth_tx_hash: Vec<bool> =
            BitIterator::new(block.cross_eth_txs_commitment.into_repr()).collect();
        let cross_heco_tx_hash: Vec<bool> =
            BitIterator::new(block.cross_heco_txs_commitment.into_repr()).collect();
        let cross_sol_tx_hash: Vec<bool> =
            BitIterator::new(block.cross_sol_txs_commitment.into_repr()).collect();
        rolling_hash.extend(cross_bsc_tx_hash);
        rolling_hash.extend(cross_eth_tx_hash);
        rolling_hash.extend(cross_heco_tx_hash);
        rolling_hash.extend(cross_sol_tx_hash);

        let mut hash_result = [0u8; 32];
        let mut h = Sha256::new();
        h.input(&be_bit_vector_into_bytes(&rolling_hash));
        h.result(&mut hash_result[..]);

        let mut block_commitment_repr = E::Fr::zero().into_repr();
        block_commitment_repr
            .read_be(&hash_result[..])
            .expect("pack hash as field element");

        let rolling_commitment = AllocatedNum::alloc(cs, || Ok(rolling_commitment))?;
        let cross_bsc_txs_commitment =
            AllocatedNum::alloc(cs, || Ok(block.cross_bsc_txs_commitment))?;
        let cross_eth_txs_commitment =
            AllocatedNum::alloc(cs, || Ok(block.cross_eth_txs_commitment))?;
        let cross_heco_txs_commitment =
            AllocatedNum::alloc(cs, || Ok(block.cross_heco_txs_commitment))?;
        let cross_sol_txs_commitment =
            AllocatedNum::alloc(cs, || Ok(block.cross_sol_txs_commitment))?;
        let mut block_to_public_input = Vec::new();
        block_to_public_input.extend(allocated_num_to_aligned_big_endian(
            cs,
            &rolling_commitment,
        )?);
        block_to_public_input.extend(allocated_num_to_aligned_big_endian(
            cs,
            &cross_bsc_txs_commitment,
        )?);
        block_to_public_input.extend(allocated_num_to_aligned_big_endian(
            cs,
            &cross_eth_txs_commitment,
        )?);
        block_to_public_input.extend(allocated_num_to_aligned_big_endian(
            cs,
            &cross_heco_txs_commitment,
        )?);
        block_to_public_input.extend(allocated_num_to_aligned_big_endian(
            cs,
            &cross_sol_txs_commitment,
        )?);

        let block_commitment = sha256_circuit_hash(cs, &block_to_public_input)?;

        let block_commitment = aligned_big_endian_to_allocated_num(cs, block_commitment)?;
        assert_eq!(
            block_commitment.get_value().unwrap(),
            E::Fr::from_repr(block_commitment_repr).unwrap()
        );

        // Todo zklink: 截掉前三个bit，reserve bits

        Ok(AllocatedBlock {
            rolling_commitment,
            block_commitment,
            chain_id,
            cross_bsc_txs_commitment,
            cross_eth_txs_commitment,
            cross_heco_txs_commitment,
            cross_sol_txs_commitment,
        })
    }
}

// rolling hash
#[derive(Debug, Clone)]
pub struct BlockWitness<E: RescueEngine> {
    // first part
    block_number: Option<E::Fr>,
    validator_address: Option<E::Fr>,
    // second part
    old_root: Option<E::Fr>,
    // third part
    new_root: Option<E::Fr>,
    // fourth part
    block_timestamp: Option<E::Fr>,
    // fifth part
    public_data_commitment: Vec<bool>,
    op_offset_commitment: Vec<bool>,

    // sixth part
    cross_bsc_txs_commitment: E::Fr,
    cross_eth_txs_commitment: E::Fr,
    cross_heco_txs_commitment: E::Fr,
    cross_sol_txs_commitment: E::Fr,
}

impl<E: RescueEngine> Default for BlockWitness<E> {
    fn default() -> Self {
        BlockWitness {
            block_number: None,
            validator_address: None,
            old_root: None,
            new_root: None,
            block_timestamp: None,
            public_data_commitment: vec![],
            op_offset_commitment: vec![],
            cross_bsc_txs_commitment: E::Fr::zero(),
            cross_eth_txs_commitment: E::Fr::zero(),
            cross_heco_txs_commitment: E::Fr::zero(),
            cross_sol_txs_commitment: E::Fr::zero(),
        }
    }
}

pub fn be_bit_vector_into_bytes(bits: &[bool]) -> Vec<u8> {
    let mut bytes: Vec<u8> = vec![];

    let byte_chunks = bits.chunks(8);

    for byte_chunk in byte_chunks {
        let mut byte = 0u8;
        // pack just in order
        for (i, bit) in byte_chunk.iter().enumerate() {
            if *bit {
                byte |= 1 << (7 - i);
            }
        }
        bytes.push(byte);
    }

    bytes
}

#[allow(clippy::too_many_arguments)]
pub fn public_data_commitment<E: RescueEngine>(
    crt_accumulator: E::Fr,
    pubdata_bits: &[bool],
    initial_root: Option<E::Fr>,
    new_root: Option<E::Fr>,
    validator_address: Option<E::Fr>,
    block_number: Option<E::Fr>,
    timestamp: Option<E::Fr>,
    offset_commitment: &[bool],
) -> E::Fr {
    let mut public_data_initial_bits = vec![];

    // these two are BE encodings because an iterator is BE. This is also an Ethereum standard behavior

    // Add block_number to public data
    let block_number_bits: Vec<bool> =
        BitIterator::new(block_number.unwrap().into_repr()).collect();

    public_data_initial_bits.extend(vec![false; 256 - block_number_bits.len()]);
    public_data_initial_bits.extend(block_number_bits.into_iter());

    // Add validator_id to public data
    let validator_id_bits: Vec<bool> =
        BitIterator::new(validator_address.unwrap().into_repr()).collect();

    public_data_initial_bits.extend(vec![false; 256 - validator_id_bits.len()]);
    public_data_initial_bits.extend(validator_id_bits.into_iter());

    assert_eq!(public_data_initial_bits.len(), 512);

    // hash [0000...block_number_bits | 0000...validator_id_bits]
    let bytes_to_hash = be_bit_vector_into_bytes(&public_data_initial_bits);
    let mut h = Sha256::new();
    h.input(&bytes_to_hash);
    let mut hash_result = [0u8; 32];
    h.result(&mut hash_result[..]);

    // hash old root
    let old_root_bits: Vec<bool> = BitIterator::new(initial_root.unwrap().into_repr()).collect();
    let mut packed_old_root_bits = vec![false; 256 - old_root_bits.len()];
    packed_old_root_bits.extend(old_root_bits);

    let packed_old_root_bytes = be_bit_vector_into_bytes(&packed_old_root_bits);

    let mut packed_with_old_root = vec![];
    packed_with_old_root.extend(hash_result.iter());
    packed_with_old_root.extend(packed_old_root_bytes);

    h = Sha256::new();
    h.input(&packed_with_old_root);
    hash_result = [0u8; 32];
    h.result(&mut hash_result[..]);

    // hash new root
    let new_root_bits: Vec<bool> = BitIterator::new(new_root.unwrap().into_repr()).collect();
    let mut packed_new_root_bits = vec![false; 256 - new_root_bits.len()];
    packed_new_root_bits.extend(new_root_bits);

    let packed_new_root_bytes = be_bit_vector_into_bytes(&packed_new_root_bits);

    let mut packed_with_new_root = vec![];
    packed_with_new_root.extend(hash_result.iter());
    packed_with_new_root.extend(packed_new_root_bytes);

    h = Sha256::new();
    h.input(&packed_with_new_root);
    hash_result = [0u8; 32];
    h.result(&mut hash_result[..]);

    // hash timestamp
    let timstamp_unpadded_bits: Vec<bool> =
        BitIterator::new(timestamp.unwrap().into_repr()).collect();
    let mut timestamp_bits = vec![false; 256 - timstamp_unpadded_bits.len()];
    timestamp_bits.extend(timstamp_unpadded_bits.into_iter());
    let timestamp_bytes = be_bit_vector_into_bytes(&timestamp_bits);
    let mut packed_with_timestamp = vec![];
    packed_with_timestamp.extend(hash_result.iter());
    packed_with_timestamp.extend(timestamp_bytes.iter());

    h = Sha256::new();
    h.input(&packed_with_timestamp);
    hash_result = [0u8; 32];
    h.result(&mut hash_result[..]);

    // hash pubdata_bits + offset_commitment
    let pubdata_with_offset = [pubdata_bits, offset_commitment].concat();
    let pubdata_bytes = be_bit_vector_into_bytes(&pubdata_with_offset);

    let mut pubdata_offset_bytes = vec![];
    pubdata_offset_bytes.extend(hash_result.iter());
    pubdata_offset_bytes.extend(pubdata_bytes);

    h = Sha256::new();
    h.input(&pubdata_offset_bytes);
    hash_result = [0u8; 32];
    h.result(&mut hash_result[..]);

    // hash cross rollup transactions accumulator
    let mut crt_accumulator: Vec<bool> = BitIterator::new(crt_accumulator.into_repr()).collect();
    crt_accumulator.extend(vec![false; 256 - crt_accumulator.len()]);
    let accumulator_bytes = be_bit_vector_into_bytes(&crt_accumulator);

    let mut final_bytes = vec![];
    final_bytes.extend(hash_result.iter());
    final_bytes.extend(accumulator_bytes);

    h = Sha256::new();
    h.input(&final_bytes);
    hash_result = [0u8; 32];
    h.result(&mut hash_result[..]);

    hash_result[0] &= 0x1f; // temporary solution, this nullifies top bits to be encoded into field element correctly

    let mut repr = E::Fr::zero().into_repr();
    repr.read_be(&hash_result[..])
        .expect("pack hash as field element");

    E::Fr::from_repr(repr).unwrap()
}
