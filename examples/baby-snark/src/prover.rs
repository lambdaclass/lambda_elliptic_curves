use crate::{common::*, setup::ProvingKey, ssp::SquareSpanProgram};
use lambdaworks_math::{cyclic_group::IsGroup, msm::pippenger::msm};
pub struct Proof {
    pub h: G1Point,
    pub v_w: G1Point,
    pub v_w_prime: G2Point,
    pub b_w: G1Point,
}

#[derive(Debug)]
pub enum Error {
    WrongWitness,
    FirstInputElementIsNotOne,
}

pub struct Prover;
impl Prover {
    pub fn prove(
        inputs: &[FrElement],
        ssp: &SquareSpanProgram,
        pk: &ProvingKey,
    ) -> Result<Proof, Error> {
        if inputs[0].ne(&FrElement::one()) {
            return Err(Error::FirstInputElementIsNotOne);
        }
        if !ssp.check_valid(inputs) {
            return Err(Error::WrongWitness);
        }

        // Sample randomness for hiding
        let delta = sample_fr_elem();

        let h_coefficients = ssp
            .calculate_h_coefficients(inputs, &delta)
            .iter()
            .map(|elem| elem.representative())
            .collect::<Vec<_>>();

        let h = msm(&h_coefficients, &pk.k_powers_of_tau_g1).unwrap();
        let w = inputs
            .iter()
            .skip(ssp.number_of_public_inputs)
            .map(|elem| elem.representative())
            .collect::<Vec<_>>();

        let v_w = msm(&w, &pk.u_tau_g1)
            .unwrap()
            .operate_with(&pk.t_tau_g1.operate_with_self(delta.representative()));

        let v_w_prime = msm(&w, &pk.u_tau_g2)
            .unwrap()
            .operate_with(&pk.t_tau_g2.operate_with_self(delta.representative()));

        let b_w = msm(&w, &pk.beta_u_tau_g1)
            .unwrap()
            .operate_with(&pk.beta_t_tau_g1.operate_with_self(delta.representative()));

        Ok(Proof {
            h,
            v_w,
            v_w_prime,
            b_w,
        })
    }
}
