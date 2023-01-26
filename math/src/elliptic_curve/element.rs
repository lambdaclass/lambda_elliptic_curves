use crate::cyclic_group::IsCyclicBilinearGroup;
use crate::elliptic_curve::traits::{HasDistortionMap, HasEllipticCurveOperations};
use crate::field::element::FieldElement;
use std::fmt::Debug;
use std::marker::PhantomData;

/// Represents an elliptic curve point using the projective short Weierstrass form:
/// y^2 * z = x^3 + a * x * z^2 + b * z^3,
/// where `x`, `y` and `z` variables are field elements.
#[derive(Debug, Clone)]
pub struct EllipticCurveElement<E: HasEllipticCurveOperations> {
    value: [FieldElement<E::BaseField>; 3],
    elliptic_curve: PhantomData<E>,
}

impl<E: HasEllipticCurveOperations> EllipticCurveElement<E> {
    /// Creates an elliptic curve point giving the projective [x: y: z] coordinates.
    pub fn new(value: [FieldElement<E::BaseField>; 3]) -> Self {
        assert_eq!(
            E::defining_equation(&value),
            FieldElement::zero(),
            "Point ({:?}) does not belong to the elliptic curve.",
            &value
        );
        Self {
            value,
            elliptic_curve: PhantomData,
        }
    }

    /// Returns the `x` coordinate of the point.
    pub fn x(&self) -> &FieldElement<E::BaseField> {
        &self.value[0]
    }

    /// Returns the `y` coordinate of the point.
    pub fn y(&self) -> &FieldElement<E::BaseField> {
        &self.value[1]
    }

    /// Returns the `z` coordinate of the point.
    pub fn z(&self) -> &FieldElement<E::BaseField> {
        &self.value[2]
    }

    /// Creates the same point in affine coordinates. That is,
    /// returns [x / z: y / z: 1] where `self` is [x: y: z].
    /// Panics if `self` is the point at infinity.
    pub fn to_affine(&self) -> Self {
        Self {
            value: E::affine(&self.value),
            elliptic_curve: PhantomData,
        }
    }

    /// Returns the Weil pairing between `self` and `other`.
    pub fn weil_pairing(&self, other: &Self) -> FieldElement<E::BaseField> {
        E::weil_pairing(&self.value, &other.value)
    }

    /// Returns the Tate pairing between `self` and `other`.
    pub fn tate_pairing(&self, other: &Self) -> FieldElement<E::BaseField> {
        E::tate_pairing(&self.value, &other.value)
    }
}

impl<E: HasEllipticCurveOperations> PartialEq for EllipticCurveElement<E> {
    fn eq(&self, other: &Self) -> bool {
        E::eq(&self.value, &other.value)
    }
}

impl<E: HasEllipticCurveOperations> Eq for EllipticCurveElement<E> {}

impl<E: HasEllipticCurveOperations + HasDistortionMap> IsCyclicBilinearGroup
    for EllipticCurveElement<E>
{
    type PairingOutput = FieldElement<E::BaseField>;

    fn generator() -> Self {
        Self::new([
            E::generator_affine_x(),
            E::generator_affine_y(),
            FieldElement::one(),
        ])
    }

    fn neutral_element() -> Self {
        Self::new(E::neutral_element())
    }

    /// Computes the addition of `self` and `other`.
    /// Taken from "Moonmath" (Algorithm 7, page 89)
    fn operate_with(&self, other: &Self) -> Self {
        Self::new(E::add(&self.value, &other.value))
    }

    /// Computes a Type 1 Tate pairing between `self` and `other.
    /// See "Pairing for beginners" from Craig Costello, section 4.2 Pairing types, page 58.
    /// Note that a distorsion map is applied to `other` before using the Tate pairing.
    /// So this method can be called with two field extension elements from the base field.
    fn pairing(&self, other: &Self) -> Self::PairingOutput {
        let [qx, qy, qz] = E::distorsion_map(&other.value);
        Self::tate_pairing(self, &Self::new([qx, qy, qz]))
    }
}

#[cfg(test)]
mod tests {
    use crate::cyclic_group::IsCyclicBilinearGroup;
    use crate::elliptic_curve::curves::test_curve::{
        QuadraticNonResidue, TestCurve, ORDER_P, ORDER_R,
    };
    use crate::field::fields::u64_prime_field::U64PrimeField;
    use crate::{
        elliptic_curve::element::EllipticCurveElement,
        field::{
            fields::u64_prime_field::U64FieldElement,
            quadratic_extension::QuadraticExtensionFieldElement,
        },
    };

    #[allow(clippy::upper_case_acronyms)]
    type FEE = QuadraticExtensionFieldElement<U64PrimeField<ORDER_P>, QuadraticNonResidue>;

    // This tests only apply for the specific curve found in the configuration file.
    #[test]
    fn create_valid_point_works() {
        let point =
            EllipticCurveElement::<TestCurve>::new([FEE::from(35), FEE::from(31), FEE::from(1)]);
        assert_eq!(*point.x(), FEE::from(35));
        assert_eq!(*point.y(), FEE::from(31));
        assert_eq!(*point.z(), FEE::from(1));
    }

    #[test]
    #[should_panic]
    fn create_invalid_points_panicks() {
        EllipticCurveElement::<TestCurve>::new([FEE::from(0), FEE::from(1), FEE::from(1)]);
    }

    #[test]
    fn equality_works() {
        let g = EllipticCurveElement::<TestCurve>::generator();
        let g2 = g.operate_with(&g);
        assert_ne!(&g2, &g);
    }

    #[test]
    fn operate_with_self_works_1() {
        let g = EllipticCurveElement::<TestCurve>::generator();
        assert_eq!(g.operate_with(&g).operate_with(&g), g.operate_with_self(3));
    }

    #[test]
    fn operate_with_self_works_2() {
        let mut point_1 = EllipticCurveElement::<TestCurve>::generator();
        point_1 = point_1.operate_with_self(ORDER_R as u128);
        assert_eq!(
            point_1,
            EllipticCurveElement::<TestCurve>::neutral_element()
        );
    }

    #[test]
    fn doubling_a_point_works() {
        let point =
            EllipticCurveElement::<TestCurve>::new([FEE::from(35), FEE::from(31), FEE::from(1)]);
        let expected_result =
            EllipticCurveElement::<TestCurve>::new([FEE::from(25), FEE::from(29), FEE::from(1)]);
        assert_eq!(point.operate_with_self(2).to_affine(), expected_result);
    }

    #[test]
    fn test_weil_pairing() {
        type FE = U64FieldElement<ORDER_P>;
        let pa =
            EllipticCurveElement::<TestCurve>::new([FEE::from(35), FEE::from(31), FEE::from(1)]);
        let pb = EllipticCurveElement::<TestCurve>::new([
            FEE::new([FE::new(24), FE::new(0)]),
            FEE::new([FE::new(0), FE::new(31)]),
            FEE::from(1),
        ]);
        let expected_result = FEE::new([FE::new(46), FE::new(3)]);

        let result_weil = EllipticCurveElement::<TestCurve>::weil_pairing(&pa, &pb);
        assert_eq!(result_weil, expected_result);
    }

    #[test]
    fn test_tate_pairing() {
        type FE = U64FieldElement<ORDER_P>;
        let pa =
            EllipticCurveElement::<TestCurve>::new([FEE::from(35), FEE::from(31), FEE::from(1)]);
        let pb = EllipticCurveElement::<TestCurve>::new([
            FEE::new([FE::new(24), FE::new(0)]),
            FEE::new([FE::new(0), FE::new(31)]),
            FEE::from(1),
        ]);
        let expected_result = FEE::new([FE::new(42), FE::new(19)]);

        let result_weil = EllipticCurveElement::<TestCurve>::tate_pairing(&pa, &pb);
        assert_eq!(result_weil, expected_result);
    }
}
