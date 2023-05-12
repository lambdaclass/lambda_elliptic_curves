use lambdaworks_math::{
    field::{
        element::FieldElement,
        fields::montgomery_backed_prime_fields::{IsModulus, MontgomeryBackendPrimeField},
    },
    traits::ByteConversion,
    unsigned_integer::element::UnsignedInteger,
};
use sha3::{Digest, Sha3_256};

use super::{hash_to_field::hash_to_field, traits::IsCryptoHash};

const DST: &[u8; 32] = b"LAMBDA00-MONTGOMERY_XMD:SHA3-256";

pub struct Sha3Hasher;

/// Sha3 Hasher used over fields
/// Notice while it's generic over F, it's only generates enough randomness for fields of at most 256 bits
impl Sha3Hasher {
    pub const fn new() -> Self {
        Self
    }
}
impl<M: IsModulus<UnsignedInteger<N>> + Clone, const N: usize>
    IsCryptoHash<MontgomeryBackendPrimeField<M, N>> for Sha3Hasher
{
    fn hash_one(
        &self,
        input: &FieldElement<MontgomeryBackendPrimeField<M, N>>,
    ) -> FieldElement<MontgomeryBackendPrimeField<M, N>> {
        let mut hasher = Sha3_256::new();
        hasher.update(input.to_bytes_be());
        expand_and_convert_to_field(&hasher.finalize())
    }

    fn hash_two(
        &self,
        left: &FieldElement<MontgomeryBackendPrimeField<M, N>>,
        right: &FieldElement<MontgomeryBackendPrimeField<M, N>>,
    ) -> FieldElement<MontgomeryBackendPrimeField<M, N>> {
        let mut hasher = Sha3_256::new();
        hasher.update(left.to_bytes_be());
        hasher.update(right.to_bytes_be());
        expand_and_convert_to_field(&hasher.finalize())
    }

    fn hash_many(
        &self,
        elements: &[FieldElement<MontgomeryBackendPrimeField<M, N>>],
    ) -> FieldElement<MontgomeryBackendPrimeField<M, N>> {
        let mut serialized_elements = Vec::with_capacity(N * 8 * elements.len());
        for elem in elements {
            serialized_elements.extend(elem.to_bytes_be());
        }
        let mut hasher = Sha3_256::new();
        hasher.update(&serialized_elements);
        expand_and_convert_to_field(&hasher.finalize())
    }
}

fn expand_and_convert_to_field<M: IsModulus<UnsignedInteger<N>> + Clone, const N: usize>(
    bytes: &[u8],
) -> FieldElement<MontgomeryBackendPrimeField<M, N>> {
    let l = compute_length(M::MODULUS);
    let expanded = expand_message(bytes, DST, l as u64).unwrap();
    hash_to_field(&expanded, l, 1).first().unwrap().clone()
}

fn expand_message(msg: &[u8], dst: &[u8], len_in_bytes: u64) -> Result<Vec<u8>, String> {
    let b_in_bytes = Sha3_256::output_size() as u64;

    let ell = (len_in_bytes + b_in_bytes - 1) / b_in_bytes;
    if ell > 255 {
        return Err("Abort".to_string());
    }

    let dst_prime: Vec<u8> = [dst, &i2osp(dst.len() as u64, 1)].concat();
    let z_pad = i2osp(0, 64);
    let l_i_b_str = i2osp(len_in_bytes, 2);
    let msg_prime = [
        z_pad,
        msg.to_vec(),
        l_i_b_str,
        i2osp(0, 1),
        dst_prime.clone(),
    ]
    .concat();
    let b_0: Vec<u8> = Sha3_256::digest(msg_prime).to_vec();
    let a = [b_0.clone(), i2osp(1, 1), dst_prime.clone()].concat();
    let b_1 = Sha3_256::digest(a).to_vec();

    let mut b_vals = Vec::<Vec<u8>>::with_capacity(ell as usize * b_in_bytes as usize);
    b_vals.push(b_1);
    for idx in 1..ell {
        let aux = strxor(&b_0, &b_vals[idx as usize - 1]);
        let b_i = [aux, i2osp(idx, 1), dst_prime.clone()].concat();
        b_vals.push(Sha3_256::digest(b_i).to_vec());
    }

    let mut b_vals = b_vals.concat();
    b_vals.truncate(len_in_bytes as usize);

    Ok(b_vals)
}

fn i2osp(x: u64, length: u64) -> Vec<u8> {
    let mut x_aux = x;
    let mut digits = Vec::new();
    while x_aux != 0 {
        digits.push((x_aux % 256) as u8);
        x_aux /= 256;
    }
    digits.resize(digits.len() + (length - digits.len() as u64) as usize, 0);
    digits.reverse();
    digits
}

fn strxor(a: &[u8], b: &[u8]) -> Vec<u8> {
    a.iter().zip(b).map(|(a, b)| a ^ b).collect()
}

fn compute_length<const N: usize>(order: UnsignedInteger<N>) -> usize {
    //L = ceil((ceil(log2(p)) + k) / 8), where k is the security parameter of the cryptosystem (e.g. k = ceil(log2(p) / 2))
    let log2_p = order.limbs.len() << 3;
    ((log2_p << 3) + (log2_p << 2)) >> 3
}
