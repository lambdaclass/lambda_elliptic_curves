use super::field_extension::BLS12381PrimeField;
use crate::{
    elliptic_curve::short_weierstrass::{
        curves::bls12_381::curve::BLS12381Curve, point::ShortWeierstrassProjectivePoint,
    },
    field::element::FieldElement,
};
use core::cmp::Ordering;

use crate::{
    cyclic_group::IsGroup, elliptic_curve::traits::FromAffine, errors::ByteConversionError,
    traits::ByteConversion,
};

pub type G1Point = ShortWeierstrassProjectivePoint<BLS12381Curve>;
pub type BLS12381FieldElement = FieldElement<BLS12381PrimeField>;

pub fn decompress_g1_point(input_bytes: &mut [u8; 48]) -> Result<G1Point, ByteConversionError> {
    let first_byte = input_bytes.first().unwrap();
    // We get the 3 most significant bits
    let prefix_bits = first_byte >> 5;
    let first_bit = (prefix_bits & 4_u8) >> 2;
    // If first bit is not 1, then the value is not compressed.
    if first_bit != 1 {
        return Err(ByteConversionError::ValueNotCompressed);
    }
    let second_bit = (prefix_bits & 2_u8) >> 1;
    // If the second bit is 1, then the compressed point is the
    // point at infinity and we return it directly.
    if second_bit == 1 {
        return Ok(G1Point::neutral_element());
    }
    let third_bit = prefix_bits & 1_u8;

    let first_byte_without_control_bits = (first_byte << 3) >> 3;
    input_bytes[0] = first_byte_without_control_bits;

    let x = BLS12381FieldElement::from_bytes_be(input_bytes)?;

    // We apply the elliptic curve formula to know the y^2 value.
    let y_squared = x.pow(3_u16) + BLS12381FieldElement::from(4);

    let (y_sqrt_1, y_sqrt_2) = &y_squared.sqrt().ok_or(ByteConversionError::InvalidValue)?;

    // we call "negative" to the greate root,
    // if the third bit is 1, we take this grater value.
    // Otherwise, we take the second one.
    let y = match (
        y_sqrt_1.representative().cmp(&y_sqrt_2.representative()),
        third_bit,
    ) {
        (Ordering::Greater, 0) => y_sqrt_2,
        (Ordering::Greater, _) => y_sqrt_1,
        (Ordering::Less, 0) => y_sqrt_1,
        (Ordering::Less, _) => y_sqrt_2,
        (Ordering::Equal, _) => y_sqrt_1,
    };

    let point =
        G1Point::from_affine(x, y.clone()).map_err(|_| ByteConversionError::InvalidValue)?;

    point
        .is_in_subgroup()
        .then_some(point)
        .ok_or(ByteConversionError::PointNotInSubgroup)
}

#[cfg(feature = "alloc")]
pub fn compress_g1_point(point: &G1Point) -> alloc::vec::Vec<u8> {
    if *point == G1Point::neutral_element() {
        // point is at infinity
        let mut x_bytes = alloc::vec![0_u8; 48];
        x_bytes[0] |= 1 << 7;
        x_bytes[0] |= 1 << 6;
        x_bytes
    } else {
        // point is not at infinity
        let point_affine = point.to_affine();
        let x = point_affine.x();
        let y = point_affine.y();

        let mut x_bytes = x.to_bytes_be();

        // Set first bit to to 1 indicate this is compressed element.
        x_bytes[0] |= 1 << 7;

        let y_neg = core::ops::Neg::neg(y);
        if y_neg.representative() < y.representative() {
            x_bytes[0] |= 1 << 5;
        }
        x_bytes
    }
}

#[cfg(test)]
mod tests {
    use super::{BLS12381FieldElement, G1Point};
    use crate::elliptic_curve::short_weierstrass::curves::bls12_381::curve::BLS12381Curve;
    use crate::elliptic_curve::traits::{FromAffine, IsEllipticCurve};

    #[cfg(feature = "alloc")]
    use super::compress_g1_point;
    use super::decompress_g1_point;
    use crate::{
        cyclic_group::IsGroup, traits::ByteConversion, unsigned_integer::element::UnsignedInteger,
    };

    #[test]
    fn test_zero_point() {
        let g1 = BLS12381Curve::generator();

        assert!(g1.is_in_subgroup());
        let new_x = BLS12381FieldElement::zero();
        let new_y = BLS12381FieldElement::one() + BLS12381FieldElement::one();

        let false_point2 = G1Point::from_affine(new_x, new_y).unwrap();

        assert!(!false_point2.is_in_subgroup());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_g1_compress_generator() {
        let g = BLS12381Curve::generator();
        let mut compressed_g = compress_g1_point(&g);
        let first_byte = compressed_g.first().unwrap();

        let first_byte_without_control_bits = (first_byte << 3) >> 3;
        compressed_g[0] = first_byte_without_control_bits;

        let compressed_g_x = BLS12381FieldElement::from_bytes_be(&compressed_g).unwrap();
        let g_x = g.x();

        assert_eq!(*g_x, compressed_g_x);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_g1_compress_point_at_inf() {
        let inf = G1Point::neutral_element();
        let compressed_inf = compress_g1_point(&inf);
        let first_byte = compressed_inf.first().unwrap();

        assert_eq!(*first_byte >> 6, 3_u8);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_compress_decompress_generator() {
        let g = BLS12381Curve::generator();
        let compressed_g = compress_g1_point(&g);
        let mut compressed_g_slice: [u8; 48] = compressed_g.try_into().unwrap();

        let decompressed_g = decompress_g1_point(&mut compressed_g_slice).unwrap();

        assert_eq!(g, decompressed_g);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_compress_decompress_2g() {
        let g = BLS12381Curve::generator();
        // calculate g point operate with itself
        let g_2 = g.operate_with_self(UnsignedInteger::<4>::from("2"));

        let compressed_g2 = compress_g1_point(&g_2);
        let mut compressed_g2_slice: [u8; 48] = compressed_g2.try_into().unwrap();

        let decompressed_g2 = decompress_g1_point(&mut compressed_g2_slice).unwrap();

        assert_eq!(g_2, decompressed_g2);
    }
}
