/// Example curve taken from the book "Pairing for beginners", page 57.
/// Defines the basic constants needed to describe a curve in the short Weierstrass form.
/// This small curve has only 5 elements.
use crate::{
    elliptic_curve::traits::{HasDistortionMap, HasEllipticCurveOperations},
    field::{
        element::FieldElement,
        fields::u64_prime_field::U64PrimeField,
        quadratic_extension::{HasQuadraticNonResidue, QuadraticExtensionField},
    },
};

/// Order of the base field (e.g.: order of the coordinates)
const ORDER_P: u64 = 59;

/// Order of the subgroup of the curve.
const ORDER_R: u64 = 5;

/// In F59 the element -1 is not a square. We use this property
/// to construct a Quadratic Field Extension out of it by adding
/// its square root.
#[derive(Debug, Clone)]
pub struct QuadraticNonResidue;
impl HasQuadraticNonResidue<U64PrimeField<ORDER_P>> for QuadraticNonResidue {
    fn residue() -> FieldElement<U64PrimeField<ORDER_P>> {
        -FieldElement::one()
    }
}

/// The description of the curve.
#[derive(Clone, Debug)]
pub struct TestCurve;
impl HasEllipticCurveOperations for TestCurve {
    type BaseField = QuadraticExtensionField<U64PrimeField<ORDER_P>, QuadraticNonResidue>;

    ///
    fn a() -> FieldElement<Self::BaseField> {
        FieldElement::from(1)
    }

    fn b() -> FieldElement<Self::BaseField> {
        FieldElement::from(0)
    }

    fn generator_affine_x() -> FieldElement<Self::BaseField> {
        FieldElement::from(35)
    }

    fn generator_affine_y() -> FieldElement<Self::BaseField> {
        FieldElement::from(31)
    }

    fn embedding_degree() -> u32 {
        2
    }

    fn order_r() -> u64 {
        ORDER_R
    }

    fn order_p() -> u64 {
        ORDER_P
    }
}

impl HasDistortionMap for TestCurve {
    fn distorsion_map(
        p: &[FieldElement<Self::BaseField>; 3],
    ) -> [FieldElement<Self::BaseField>; 3] {
        let (x, y, z) = (&p[0], &p[1], &p[2]);
        let t = FieldElement::new([FieldElement::zero(), FieldElement::one()]);
        [-x, y * t, z.clone()]
    }
}

#[cfg(test)]
mod tests {
    use crate::cyclic_group::HasCyclicBilinearGroupStructure;
    use crate::{
        elliptic_curve::element::EllipticCurveElement,
        field::{
            fields::u64_prime_field::U64FieldElement,
            quadratic_extension::QuadraticExtensionFieldElement,
        },
    };

    use super::*;

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
