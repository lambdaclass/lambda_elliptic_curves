use super::curve::MILLER_LOOP_CONSTANT;
// We defined MILLER_LOOP_CONSTANT in curve.rs
// see https://hackmd.io/@Wimet/ry7z1Xj-2
// @Juan is this the same parameter used in the NAF representation? 
// t = 6x^2. Where x = 4965661367192848881

use super::{
    curve::BN254Curve,
    field_extension::{BN254PrimeField, Degree12ExtensionField, Degree2ExtensionField},
    twist::BN254TwistCurve,
};
use crate::{cyclic_group::IsGroup, elliptic_curve::traits::IsPairing, errors::PairingError};
use crate::{
    elliptic_curve::short_weierstrass::{
        curves::bn_254::field_extension::{Degree6ExtensionField, LevelTwoResidue},
        point::ShortWeierstrassProjectivePoint,
        traits::IsShortWeierstrass,
    },
    field::{element::FieldElement, extensions::cubic::HasCubicNonResidue},
    unsigned_integer::element::{UnsignedInteger, U256},
};
// We have to find the SUBGROUP_ORDER and see where it's used.
// In the implementation of zksync we have:
// 21888242871839275222246405745257275088548364400416034343698204186575808495617
// 30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001 (fist I coverted it into hex)
/* pub const SUBGROUP_ORDER: U256 =
    U256::from_hex_unchecked("TODO"); */

type Fp2E = FieldElement<Degree2ExtensionField>;
type Fp6E = FieldElement<Degree6ExtensionField>;
type Fp12E = FieldElement<Degree12ExtensionField>;

// Need implementation of NAF representation
// 
/// Millers loop uses to iterate the NAF representation of the MILLER_LOOP_CONSTANT
/// A NAF representation uses values: -1, 0 and 1. https://en.wikipedia.org/wiki/Non-adjacent_form.
pub const MILLER_CONSTANT_NAF: [i32; 115] = [
    1, 0, -1, 0, 0, -1, 0, -1, 0, 1, 0, -1, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0,
    -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0,
    0, 0, -1, 0, -1, 0, -1, 0, 0, -1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0
];

/*
pub struct BN254AtePairing;
impl IsPairing for BN254AtePairing {
    type G1Point = ShortWeierstrassProjectivePoint<BN254Curve>;
    type G2Point = ShortWeierstrassProjectivePoint<BN254TwistCurve>;
    type OutputField = Degree12ExtensionField;

    // Computes the product of the ate pairings for a list of point pairs.
    // To optimize the pairing computation, we compute first all the miller
    // loops and multiply each other (so that we can then do the final expon).
    fn compute_batch(
        pairs: &[(&Self::G1Point, &Self::G2Point)],
    ) -> Result<FieldElement<Self::OutputField>, PairingError> {
        let mut result = FieldElement::one();
        for (p, q) in pairs {

            // We think we can remove the condition !p.is_in_subgroup() because
            // the subgroup oF G1 is G1 (see BN254 for the rest of us).
            if !p.is_in_subgroup() || !q.is_in_subgroup() {
                return Err(PairingError::PointNotInSubgroup);
            }
            if !p.is_neutral_element() && !q.is_neutral_element() {
                let p = p.to_affine();
                let q = q.to_affine();
                result *= miller(&q, &p);
            }
        }
        Ok(final_exponentiation(&result))
    }
} */

// TODO
// We need a function that computes the double of a G2 point and its tangent line.
// In the implementation of bls381, this function also changes the t's and accumulator's (f) values.
// Initially t = Q, accumulator (f) = 1. See https://eprint.iacr.org/2010/354.pdf.

// incomplete

// Transforms t = 2t and accumulator = accumulator * l(p) where l is the tangent line of t.
fn double_accumulate_line (
    t: &mut ShortWeierstrassProjectivePoint<BN254TwistCurve>,
    p: &ShortWeierstrassProjectivePoint<BN254Curve>,
    accumulator: &mut FieldElement<Degree12ExtensionField>,
)
{
    let [x_q, y_q, z_q] = t.coordinates(); 
    // @nicole: Is it ok p as a ProjectivPoint or do we need to have it in two coordinates?
    // let [x_p, y_p] = p.to_affine().coordintes();
    let [x_p, y_p, _] = p.coordinates();
    
    let mut a = x_q.square(); // 1
    let b = y_q.square(); // 2
    let c = &b.square();// 3
    let mut d = (&b + x_q).square() - a.clone() - c; // 4
    d = d.clone().double(); //2 temp3 // 5
    let mut e = a.clone().double() + &a;  // 3 temp1 // 6
    let f = x_q + &e; // 7
    let g = f.square(); // 8
    let x_t = f - &d - &d ; // 9
    let z_t = (y_q + z_q).square() - &b - z_q.square(); // 10
    let y_t = (d - &x_t) * &e - &c.double().double().double(); //11
    d =  - ((&e * z_q.square()).double());//12
    d = x_p * d; //13 . Watchout with the order of the operation  x_p*d .d * x_p is not defined
    e = e.square() - a  - g - b.double().double();  //14
    a  = (&z_t * z_q.square()).double(); //15
    a = y_p * a;// 16 
    let a_0 = Fp6E::new([Fp2E::zero(), Fp2E::zero(), a]); //18 TODO: check the coefficient's order
    let a_1 = Fp6E::new([Fp2E::zero(), e, d]); //19 //a_1 = 0*v^2 + e*v + d

    t.0.value = [x_t, y_t, z_t];
    let l = Fp12E::new([a_1, a_0]); //l = a_0 + a_1*w
    *accumulator = accumulator.square() * l;
}
/*
//TODO
// We need a function that computes the addition of two G2 points and the line through them.
fn add_accumulate_line(
    t: &mut ShortWeierstrassProjectivePoint<BN254TwistCurve>,
    q: &ShortWeierstrassProjectivePoint<BN254TwistCurve>,
    p: &ShortWeierstrassProjectivePoint<BN254Curve>,
    accumulator: &mut FieldElement<Degree12ExtensionField>,
) {
    let [x_q, y_q, z_q] = q.coordinates();
    let mut x_t = t.x();
    let mut y_t = t.y();
    let mut z_t = t.z();
    let [x_p, y_p, _] = p.coordinates();
    
    let t0 = x_q * z_t.square(); //1
    let mut t1 = (y_q + z_t).square() - y_q.square() - z_t.square(); //2
    let t1 = t1 * z_t.square(); // 3
    let t2 = t0 - x_t; // 4
    let t3 = t2.square(); //5
    let t4 = t3.double().double(); // 6
    let t5 = t4* t2; // 7
    let mut t6 = t1 - y_t.double(); // 8
    let mut t9 = t6 * x_q;//9
    let t7 = x_t * t4; //10
    x_t = &(t6.square() -&t5 - t7.double()); //11
    z_t = &((z_t + t2).square() - z_t.square()-t3); // 12
    let mut t10 = y_q + z_t; //13
    let t8 = (t1 - x_t) * t6; //14
    let t0 = (y_t * t5).double(); // 15
    let  y_t = t8 - t0; //16
    t10 = t10.square() - y_q.square() - z_t.square(); //17  
    t9 = t9.double()-t10;  //18
    t10 = (y_p * z_t).double();//19
    t6 = -t6; //20
    t1 = (x_p * t6).double(); //21
    let l_0 = Fp6E::new([Fp2E::zero(), Fp2E::zero(), t10]); //23
    let l_1 = Fp6E::new([Fp2E::zero(), t9, t1]); //24
    t.0.value = [x_t.clone(), y_t, z_t.clone()];
    let l = Fp12E::new([l_1, l_0]); //26
    accumulator = accumulator * &l;
}
*/
#[cfg(test)]
mod tests {
    use crate::{
        cyclic_group::IsGroup, elliptic_curve::traits::IsEllipticCurve,
        unsigned_integer::element::U384,
    };

    use super::*;

    #[test]
    fn test_double_accumulate_line_doubles_point_correctly() {
        let g1 = BN254Curve::generator();
        let g2 = BN254TwistCurve::generator();
        let mut r = g2.clone();
        let mut f = FieldElement::one();
        double_accumulate_line(&mut r, &g1, &mut f);
        assert_eq!(r, g2.operate_with(&g2));
    }

}