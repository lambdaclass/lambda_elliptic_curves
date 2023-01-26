use std::fmt::Debug;
use std::marker::PhantomData;

use crate::field::element::FieldElement;
use crate::field::traits::HasFieldOperations;

/// Trait to fix a quadratic non residue.
/// Used to construct a quadratic extension field by adding
/// a square root of `residue()`.
pub trait HasQuadraticNonResidue<F: HasFieldOperations> {
    fn residue() -> FieldElement<F>;
}

/// A general quadratic extension field over `F`
/// with quadratic non residue `Q::residue()`
#[derive(Debug, Clone)]
pub struct QuadraticExtensionField<F, Q>
where
    F: HasFieldOperations,
    Q: HasQuadraticNonResidue<F> + Debug,
{
    field: PhantomData<F>,
    non_residue: PhantomData<Q>,
}

pub type QuadraticExtensionFieldElement<F, Q> = FieldElement<QuadraticExtensionField<F, Q>>;

impl<F, Q> HasFieldOperations for QuadraticExtensionField<F, Q>
where
    F: HasFieldOperations + Clone,
    Q: Clone + Debug + HasQuadraticNonResidue<F>,
{
    type BaseType = [FieldElement<F>; 2];

    /// Returns the component wise addition of `a` and `b`
    fn add(a: &[FieldElement<F>; 2], b: &[FieldElement<F>; 2]) -> [FieldElement<F>; 2] {
        [&a[0] + &b[0], &a[1] + &b[1]]
    }

    /// Returns the multiplication of `a` and `b` using the following
    /// equation:
    /// (a0 + a1 * t) * (b0 + b1 * t) = a0 * b0 + a1 * b1 * Q::residue() + (a0 * b1 + a1 * b0) * t
    /// where `t.pow(2)` equals `Q::residue()`.
    fn mul(a: &[FieldElement<F>; 2], b: &[FieldElement<F>; 2]) -> [FieldElement<F>; 2] {
        let q = Q::residue();
        [
            &a[0] * &b[0] + &a[1] * &b[1] * q,
            &a[0] * &b[1] + &a[1] * &b[0],
        ]
    }

    /// Returns the component wise subtraction of `a` and `b`
    fn sub(a: &[FieldElement<F>; 2], b: &[FieldElement<F>; 2]) -> [FieldElement<F>; 2] {
        [&a[0] - &b[0], &a[1] - &b[1]]
    }

    /// Returns the component wise negation of `a`
    fn neg(a: &[FieldElement<F>; 2]) -> [FieldElement<F>; 2] {
        [-&a[0], -&a[1]]
    }

    /// Returns the multiplicative inverse of `a`
    /// This uses the equality `(a0 + a1 * t) * (a0 - a1 * t) = a0.pow(2) - a1.pow(2) * Q::residue()`
    fn inv(a: &[FieldElement<F>; 2]) -> [FieldElement<F>; 2] {
        let inv_norm = (a[0].pow(2) - Q::residue() * a[1].pow(2)).inv();
        [&a[0] * &inv_norm, -&a[1] * inv_norm]
    }

    /// Returns the division of `a` and `b`
    fn div(a: &[FieldElement<F>; 2], b: &[FieldElement<F>; 2]) -> [FieldElement<F>; 2] {
        Self::mul(a, &Self::inv(b))
    }

    /// Returns a boolean indicating whether `a` and `b` are equal component wise.
    fn eq(a: &[FieldElement<F>; 2], b: &[FieldElement<F>; 2]) -> bool {
        a[0] == b[0] && a[1] == b[1]
    }

    /// Returns the additive neutral element of the field extension.
    fn zero() -> [FieldElement<F>; 2] {
        [FieldElement::zero(), FieldElement::zero()]
    }

    /// Returns the multiplicative neutral element of the field extension.
    fn one() -> [FieldElement<F>; 2] {
        [FieldElement::one(), FieldElement::zero()]
    }

    /// Returns the element `x * 1` where 1 is the multiplicative neutral element.
    fn from_u64(x: u64) -> Self::BaseType {
        [FieldElement::from(x), FieldElement::zero()]
    }

    /// Takes as input an element of BaseType and returns the internal representation
    /// of that element in the field.
    /// Note: for this case this is simply the identity, because the components
    /// already have correct representations.
    fn from_base_type(x: [FieldElement<F>; 2]) -> [FieldElement<F>; 2] {
        x
    }
}

#[cfg(test)]
mod tests {
    use crate::field::fields::u64_prime_field::{U64FieldElement, U64PrimeField};

    const ORDER_P: u64 = 59;

    use super::*;

    #[derive(Debug, Clone)]
    struct MyQuadraticNonResidue;
    impl HasQuadraticNonResidue<U64PrimeField<ORDER_P>> for MyQuadraticNonResidue {
        fn residue() -> FieldElement<U64PrimeField<ORDER_P>> {
            -FieldElement::one()
        }
    }

    type FE = U64FieldElement<ORDER_P>;
    type MyFieldExtensionBackend =
        QuadraticExtensionField<U64PrimeField<ORDER_P>, MyQuadraticNonResidue>;
    #[allow(clippy::upper_case_acronyms)]
    type FEE = FieldElement<MyFieldExtensionBackend>;

    #[test]
    fn test_add_1() {
        let a = FEE::new([FE::new(0), FE::new(3)]);
        let b = FEE::new([-FE::new(2), FE::new(8)]);
        let expected_result = FEE::new([FE::new(57), FE::new(11)]);
        assert_eq!(a + b, expected_result);
    }

    #[test]
    fn test_add_2() {
        let a = FEE::new([FE::new(12), FE::new(5)]);
        let b = FEE::new([-FE::new(4), FE::new(2)]);
        let expected_result = FEE::new([FE::new(8), FE::new(7)]);
        assert_eq!(a + b, expected_result);
    }

    #[test]
    fn test_sub_1() {
        let a = FEE::new([FE::new(0), FE::new(3)]);
        let b = FEE::new([-FE::new(2), FE::new(8)]);
        let expected_result = FEE::new([FE::new(2), FE::new(54)]);
        assert_eq!(a - b, expected_result);
    }

    #[test]
    fn test_sub_2() {
        let a = FEE::new([FE::new(12), FE::new(5)]);
        let b = FEE::new([-FE::new(4), FE::new(2)]);
        let expected_result = FEE::new([FE::new(16), FE::new(3)]);
        assert_eq!(a - b, expected_result);
    }

    #[test]
    fn test_mul_1() {
        let a = FEE::new([FE::new(0), FE::new(3)]);
        let b = FEE::new([-FE::new(2), FE::new(8)]);
        let expected_result = FEE::new([FE::new(35), FE::new(53)]);
        assert_eq!(a * b, expected_result);
    }

    #[test]
    fn test_mul_2() {
        let a = FEE::new([FE::new(12), FE::new(5)]);
        let b = FEE::new([-FE::new(4), FE::new(2)]);
        let expected_result = FEE::new([FE::new(1), FE::new(4)]);
        assert_eq!(a * b, expected_result);
    }

    #[test]
    fn test_div_1() {
        let a = FEE::new([FE::new(0), FE::new(3)]);
        let b = FEE::new([-FE::new(2), FE::new(8)]);
        let expected_result = FEE::new([FE::new(42), FE::new(19)]);
        assert_eq!(a / b, expected_result);
    }

    #[test]
    fn test_div_2() {
        let a = FEE::new([FE::new(12), FE::new(5)]);
        let b = FEE::new([-FE::new(4), FE::new(2)]);
        let expected_result = FEE::new([FE::new(4), FE::new(45)]);
        assert_eq!(a / b, expected_result);
    }

    #[test]
    fn test_pow_1() {
        let a = FEE::new([FE::new(0), FE::new(3)]);
        let b = 5;
        let expected_result = FEE::new([FE::new(0), FE::new(7)]);
        assert_eq!(a.pow(b), expected_result);
    }

    #[test]
    fn test_pow_2() {
        let a = FEE::new([FE::new(12), FE::new(5)]);
        let b = 8;
        let expected_result = FEE::new([FE::new(52), FE::new(35)]);
        assert_eq!(a.pow(b), expected_result);
    }

    #[test]
    fn test_inv_1() {
        let a = FEE::new([FE::new(0), FE::new(3)]);
        let expected_result = FEE::new([FE::new(0), FE::new(39)]);
        assert_eq!(a.inv(), expected_result);
    }

    #[test]
    fn test_inv() {
        let a = FEE::new([FE::new(12), FE::new(5)]);
        let expected_result = FEE::new([FE::new(28), FE::new(8)]);
        assert_eq!(a.inv(), expected_result);
    }
}
