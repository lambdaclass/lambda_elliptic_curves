use crate::{common::*, setup::ProvingKey, ssp::SquareSpanProgram};
use lambdaworks_math::msm::pippenger::msm;
pub struct Proof {
    pub h: G1Point,
    pub v_w: G1Point,
    pub v_w_prime: G2Point,
    pub b_w: G1Point,
}

pub struct Prover;
impl Prover {
    pub fn prove(w: &[FrElement], ssp: &SquareSpanProgram, pk: &ProvingKey) -> Proof {
        let h_coefficients = ssp
            .calculate_h_coefficients(w)
            .iter()
            .map(|elem| elem.representative())
            .collect::<Vec<_>>();

        let h = msm(&h_coefficients, &pk.k_powers_of_tau_g1).unwrap();

        let w = w
            .iter()
            .map(|elem| elem.representative())
            .collect::<Vec<_>>();

        let v_w = msm(&w, &pk.u_tau_g1).unwrap();

        let v_w_prime = msm(&w, &pk.u_tau_g2).unwrap();

        let b_w = msm(&w, &pk.beta_u_tau_g1).unwrap();

        Proof {
            h,
            v_w,
            v_w_prime,
            b_w,
        }
    }
}
