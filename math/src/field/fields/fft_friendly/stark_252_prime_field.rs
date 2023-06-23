use crate::{
    field::{
        element::FieldElement,
        fields::montgomery_backed_prime_fields::{IsModulus, U256PrimeField},
        traits::IsFFTField,
    },
    unsigned_integer::element::{UnsignedInteger, U256},
};

#[derive(Clone, Debug)]
pub struct MontgomeryConfigStark252PrimeField;
impl IsModulus<U256> for MontgomeryConfigStark252PrimeField {
    const MODULUS: U256 =
        U256::from_hex_unchecked("800000000000011000000000000000000000000000000000000000000000001");
}

pub type Stark252PrimeField = U256PrimeField<MontgomeryConfigStark252PrimeField>;

impl IsFFTField for Stark252PrimeField {
    const TWO_ADICITY: u64 = 48;
    // Change this line for a new function like `from_limbs`.
    const TWO_ADIC_PRIMITVE_ROOT_OF_UNITY: U256 = UnsignedInteger {
        limbs: [
            219038664817244121,
            2879838607450979157,
            15244050560987562958,
            16338897044258952332,
        ],
    };

    fn field_name() -> &'static str {
        "stark256"
    }
}

impl FieldElement<Stark252PrimeField> {
    /// No std version of `to_bytes_le` from `ByteConversion` trait
    /// This follows the convention used by
    /// Starkware and Lambdaclass Cairo VM It's the same as ByteConversion to_bytes_le.
    pub fn to_bytes_le(&self) -> [u8; 32] {
        let limbs = self.representative().limbs;
        let mut bytes: [u8; 32] = [0; 32];

        for i in (0..4).rev() {
            let limb_bytes = limbs[i].to_le_bytes();
            for j in 0..8 {
                // i = 3 ->
                bytes[(3 - i) * 8 + j] = limb_bytes[j]
            }
        }
        bytes
    }
}

#[cfg(test)]
mod test_stark_252_bytes_ops {
    use super::Stark252PrimeField;
    use crate::{field::element::FieldElement, traits::ByteConversion};

    #[test]
    #[cfg(feature = "std")]
    fn byte_serialization_for_a_number_matches_with_byte_conversion_implementation() {
        let element = FieldElement::<Stark252PrimeField>::from_hex_unchecked(
            "\
            0123456701234567\
            0123456701234567\
            0123456701234567\
            0123456701234567\
        ",
        );
        let bytes = element.to_bytes_le();
        let expected_bytes: [u8; 32] = ByteConversion::to_bytes_le(&element).try_into().unwrap();
        assert_eq!(bytes, expected_bytes);
    }

    #[test]

    fn byte_serialization_and_deserialization_works() {
        let element = FieldElement::<Stark252PrimeField>::from_hex_unchecked(
            "\
            0123456701234567\
            7654321076543210\
            7654321076543210\
            7654321076543210\
        ",
        );
        let bytes = element.to_bytes_le();
        let from_bytes = FieldElement::<Stark252PrimeField>::from_bytes_le(&bytes).unwrap();
        assert_eq!(element, from_bytes);
    }
}
