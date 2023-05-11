use lambdaworks_crypto::fiat_shamir::transcript::Transcript;
use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};

use crate::{
    air::{
        constraints::boundary::{BoundaryConstraint, BoundaryConstraints},
        context::{AirContext, ProofOptions},
        frame::Frame,
        trace::TraceTable,
        AIR,
    },
    cairo_vm::{
        cairo_mem::CairoMemory, cairo_trace::CairoTrace,
        execution_trace::build_cairo_execution_trace,
    },
    transcript_to_field, FE,
};

/// Main constraint identifiers
const INST: usize = 16;
const DST_ADDR: usize = 17;
const OP0_ADDR: usize = 18;
const OP1_ADDR: usize = 19;
const NEXT_AP: usize = 20;
const NEXT_FP: usize = 21;
const NEXT_PC_1: usize = 22;
const NEXT_PC_2: usize = 23;
const T0: usize = 24;
const T1: usize = 25;
const MUL_1: usize = 26;
const MUL_2: usize = 27;
const CALL_1: usize = 28;
const CALL_2: usize = 29;
const ASSERT_EQ: usize = 30;

// Frame row identifiers
//  - Flags
const F_DST_FP: usize = 0;
const F_OP_0_FP: usize = 1;
const F_OP_1_VAL: usize = 2;
const F_OP_1_FP: usize = 3;
const F_OP_1_AP: usize = 4;
const F_RES_ADD: usize = 5;
const F_RES_MUL: usize = 6;
const F_PC_ABS: usize = 7;
const F_PC_REL: usize = 8;
const F_PC_JNZ: usize = 9;
const F_AP_ADD: usize = 10;
const F_AP_ONE: usize = 11;
const F_OPC_CALL: usize = 12;
const F_OPC_RET: usize = 13;
const F_OPC_AEQ: usize = 14;

//  - Others
// TODO: These should probably be in the TraceTable module.
pub const FRAME_RES: usize = 16;
pub const FRAME_AP: usize = 17;
pub const FRAME_FP: usize = 18;
pub const FRAME_PC: usize = 19;
pub const FRAME_DST_ADDR: usize = 20;
pub const FRAME_OP0_ADDR: usize = 21;
pub const FRAME_OP1_ADDR: usize = 22;
pub const FRAME_INST: usize = 23;
pub const FRAME_DST: usize = 24;
pub const FRAME_OP0: usize = 25;
pub const FRAME_OP1: usize = 26;
pub const OFF_DST: usize = 27;
pub const OFF_OP0: usize = 28;
pub const OFF_OP1: usize = 29;
pub const FRAME_T0: usize = 30;
pub const FRAME_T1: usize = 31;
pub const FRAME_MUL: usize = 32;
pub const FRAME_SELECTOR: usize = 33;

// Trace layout
pub const MEM_P_TRACE_OFFSET: usize = 17;
pub const MEM_A_TRACE_OFFSET: usize = 19;

// TODO: For memory constraints and builtins, the commented fields may be useful.
#[derive(Clone)]
pub struct PublicInputs {
    pub pc_init: FE,
    pub ap_init: FE,
    pub fp_init: FE,
    pub pc_final: FE,
    pub ap_final: FE,
    // pub rc_min: u16, // minimum range check value (0 < rc_min < rc_max < 2^16)
    // pub rc_max: u16, // maximum range check value
    // pub mem: (Vec<u64>, Vec<Option<FE>>), // public memory
    // pub builtins: Vec<Builtin>, // list of builtins
    pub num_steps: usize, // number of execution steps
}

#[derive(Clone)]
pub struct CairoAIR {
    pub context: AirContext,
    pub pub_inputs: PublicInputs,
}

impl CairoAIR {
    pub fn new(proof_options: ProofOptions, trace: &CairoTrace) -> Self {
        let mut padded_num_steps = 1;
        let num_steps = trace.steps();
        while padded_num_steps < num_steps {
            padded_num_steps <<= 1;
        }
        let context = AirContext {
            options: proof_options,
            trace_length: padded_num_steps,
            trace_columns: 34,
            transition_degrees: vec![
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // Flags 0-14.
                1, // Flag 15
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // Other constraints.
            ],
            transition_exemptions: vec![1; 31],
            transition_offsets: vec![0, 1],
            num_transition_constraints: 31,
        };

        let last_step = num_steps - 1;

        let pub_inputs = PublicInputs {
            pc_init: FE::from(trace.rows[0].pc),
            ap_init: FE::from(trace.rows[0].ap),
            fp_init: FE::from(trace.rows[0].fp),
            pc_final: FE::from(trace.rows[last_step].pc),
            ap_final: FE::from(trace.rows[last_step].ap),
            num_steps,
        };

        Self {
            context,
            pub_inputs,
        }
    }
}

pub struct CairoRAPChallenges {
    pub alpha: FieldElement<Stark252PrimeField>,
    pub z: FieldElement<Stark252PrimeField>,
}

impl AIR for CairoAIR {
    type Field = Stark252PrimeField;
    type RawTrace = (CairoTrace, CairoMemory);
    type RAPChallenges = CairoRAPChallenges;

    fn build_main_trace(raw_trace: &Self::RawTrace) -> TraceTable<Self::Field> {
        build_cairo_execution_trace(&raw_trace.0, &raw_trace.1)
    }

    fn build_auxiliary_trace(
        _main_trace: &TraceTable<Self::Field>,
        _rap_challenges: &Self::RAPChallenges,
    ) -> TraceTable<Self::Field> {
        // TODO: complete with CAIRO memory auxiliary columns

        TraceTable::empty()
    }

    fn build_rap_challenges<T: Transcript>(transcript: &mut T) -> Self::RAPChallenges {
        CairoRAPChallenges {
            alpha: transcript_to_field(transcript),
            z: transcript_to_field(transcript),
        }
    }

    fn compute_transition(
        &self,
        frame: &Frame<Self::Field>,
        _rap_challenges: &Self::RAPChallenges,
    ) -> Vec<FieldElement<Self::Field>> {
        let mut constraints: Vec<FieldElement<Self::Field>> =
            vec![FE::zero(); self.num_transition_constraints()];

        compute_instr_constraints(&mut constraints, frame);
        compute_operand_constraints(&mut constraints, frame);
        compute_register_constraints(&mut constraints, frame);
        compute_opcode_constraints(&mut constraints, frame);
        enforce_selector(&mut constraints, frame);

        constraints
    }

    /// From the Cairo whitepaper, section 9.10.
    /// These are part of the register constraints.
    ///
    /// Boundary constraints:
    ///  * ap_0 = fp_0 = ap_i
    ///  * ap_t = ap_f
    ///  * pc_0 = pc_i
    ///  * pc_t = pc_f
    fn boundary_constraints(
        &self,
        _rap_challenges: &Self::RAPChallenges,
    ) -> BoundaryConstraints<Self::Field> {
        let last_step = self.context.trace_length - 1;

        let initial_pc =
            BoundaryConstraint::new(MEM_A_TRACE_OFFSET, 0, self.pub_inputs.pc_init.clone());
        let initial_ap =
            BoundaryConstraint::new(MEM_P_TRACE_OFFSET, 0, self.pub_inputs.ap_init.clone());

        let final_pc = BoundaryConstraint::new(
            MEM_A_TRACE_OFFSET,
            last_step,
            self.pub_inputs.pc_final.clone(),
        );
        let final_ap = BoundaryConstraint::new(
            MEM_P_TRACE_OFFSET,
            last_step,
            self.pub_inputs.ap_final.clone(),
        );

        let constraints = vec![initial_pc, initial_ap, final_pc, final_ap];

        BoundaryConstraints::from_constraints(constraints)
    }

    fn context(&self) -> AirContext {
        self.context.clone()
    }
}

/// From the Cairo whitepaper, section 9.10
fn compute_instr_constraints(constraints: &mut [FE], frame: &Frame<Stark252PrimeField>) {
    // These constraints are only applied over elements of the same row.
    let curr = frame.get_row(0);

    // Bit constraints
    for (i, flag) in curr[0..16].iter().enumerate() {
        constraints[i] = match i {
            0..=14 => flag * (flag - FE::one()),
            15 => flag.clone(),
            _ => panic!("Unknown flag offset"),
        };
    }

    // Instruction unpacking
    let two = FE::from(2);
    let b16 = two.pow(16u32);
    let b32 = two.pow(32u32);
    let b48 = two.pow(48u32);

    // Named like this to match the Cairo whitepaper's notation.
    let f0_squiggle = &curr[0..15]
        .iter()
        .rev()
        .fold(FE::zero(), |acc, flag| flag + &two * acc);

    constraints[INST] =
        (&curr[OFF_DST]) + b16 * (&curr[OFF_OP0]) + b32 * (&curr[OFF_OP1]) + b48 * f0_squiggle
            - &curr[FRAME_INST];
}

fn compute_operand_constraints(constraints: &mut [FE], frame: &Frame<Stark252PrimeField>) {
    // These constraints are only applied over elements of the same row.
    let curr = frame.get_row(0);

    let ap = &curr[FRAME_AP];
    let fp = &curr[FRAME_FP];
    let pc = &curr[FRAME_PC];

    let one = FE::one();
    let b15 = FE::from(2).pow(15u32);

    constraints[DST_ADDR] =
        &curr[F_DST_FP] * fp + (&one - &curr[F_DST_FP]) * ap + (&curr[OFF_DST] - &b15)
            - &curr[FRAME_DST_ADDR];

    constraints[OP0_ADDR] =
        &curr[F_OP_0_FP] * fp + (&one - &curr[F_OP_0_FP]) * ap + (&curr[OFF_OP0] - &b15)
            - &curr[FRAME_OP0_ADDR];

    constraints[OP1_ADDR] = &curr[F_OP_1_VAL] * pc
        + &curr[F_OP_1_AP] * ap
        + &curr[F_OP_1_FP] * fp
        + (&one - &curr[F_OP_1_VAL] - &curr[F_OP_1_AP] - &curr[F_OP_1_FP]) * &curr[FRAME_OP0]
        + (&curr[OFF_OP1] - &b15)
        - &curr[FRAME_OP1_ADDR];
}

fn compute_register_constraints(constraints: &mut [FE], frame: &Frame<Stark252PrimeField>) {
    let curr = frame.get_row(0);
    let next = frame.get_row(1);

    let one = FE::one();
    let two = FE::from(2);

    // ap and fp constraints
    constraints[NEXT_AP] = &curr[FRAME_AP]
        + &curr[F_AP_ADD] * &curr[FRAME_RES]
        + &curr[F_AP_ONE]
        + &curr[F_OPC_CALL] * &two
        - &next[FRAME_AP];

    constraints[NEXT_FP] = &curr[F_OPC_RET] * &curr[FRAME_DST]
        + &curr[F_OPC_CALL] * (&curr[FRAME_AP] + &two)
        + (&one - &curr[F_OPC_RET] - &curr[F_OPC_CALL]) * &curr[FRAME_FP]
        - &next[FRAME_FP];

    // pc constraints
    constraints[NEXT_PC_1] = (&curr[FRAME_T1] - &curr[F_PC_JNZ])
        * (&next[FRAME_PC] - (&curr[FRAME_PC] + frame_inst_size(curr)));

    constraints[NEXT_PC_2] = &curr[FRAME_T0]
        * (&next[FRAME_PC] - (&curr[FRAME_PC] + &curr[FRAME_OP1]))
        + (&one - &curr[F_PC_JNZ]) * &next[FRAME_PC]
        - ((&one - &curr[F_PC_ABS] - &curr[F_PC_REL] - &curr[F_PC_JNZ])
            * (&curr[FRAME_PC] + frame_inst_size(curr))
            + &curr[F_PC_ABS] * &curr[FRAME_RES]
            + &curr[F_PC_REL] * (&curr[FRAME_PC] + &curr[FRAME_RES]));

    constraints[T0] = &curr[F_PC_JNZ] * &curr[FRAME_DST] - &curr[FRAME_T0];
    constraints[T1] = &curr[FRAME_T0] * &curr[FRAME_RES] - &curr[FRAME_T1];
}

fn compute_opcode_constraints(constraints: &mut [FE], frame: &Frame<Stark252PrimeField>) {
    let curr = frame.get_row(0);
    let one = FE::one();

    constraints[MUL_1] = &curr[FRAME_MUL] - (&curr[FRAME_OP0] * &curr[FRAME_OP1]);

    constraints[MUL_2] = &curr[F_RES_ADD] * (&curr[FRAME_OP0] + &curr[FRAME_OP1])
        + &curr[F_RES_MUL] * &curr[FRAME_MUL]
        + (&one - &curr[F_RES_ADD] - &curr[F_RES_MUL] - &curr[F_PC_JNZ]) * &curr[FRAME_OP1]
        - (&one - &curr[F_PC_JNZ]) * &curr[FRAME_RES];

    constraints[CALL_1] = &curr[F_OPC_CALL] * (&curr[FRAME_DST] - &curr[FRAME_FP]);

    constraints[CALL_2] =
        &curr[F_OPC_CALL] * (&curr[FRAME_OP0] - (&curr[FRAME_PC] + frame_inst_size(curr)));

    constraints[ASSERT_EQ] = &curr[F_OPC_AEQ] * (&curr[FRAME_DST] - &curr[FRAME_RES]);
}

fn enforce_selector(constraints: &mut [FE], frame: &Frame<Stark252PrimeField>) {
    let curr = frame.get_row(0);
    for result_cell in constraints.iter_mut().take(ASSERT_EQ + 1).skip(INST) {
        *result_cell = result_cell.clone() * curr[FRAME_SELECTOR].clone();
    }
}

fn frame_inst_size(frame_row: &[FE]) -> FE {
    &frame_row[F_OP_1_VAL] + FE::one()
}

#[cfg(test)]
#[cfg(debug_assertions)]
mod test {
    use lambdaworks_crypto::fiat_shamir::default_transcript::DefaultTranscript;
    use lambdaworks_math::field::element::FieldElement;

    use crate::{
        air::{context::ProofOptions, debug::validate_trace, example::cairo::CairoAIR, AIR},
        cairo_vm::{cairo_mem::CairoMemory, cairo_trace::CairoTrace},
        Domain,
    };

    #[test]
    fn check_simple_cairo_trace_evaluates_to_zero() {
        let base_dir = env!("CARGO_MANIFEST_DIR");
        let dir_trace = base_dir.to_owned() + "/src/cairo_vm/test_data/simple_program.trace";
        let dir_memory = base_dir.to_owned() + "/src/cairo_vm/test_data/simple_program.mem";

        let raw_trace = CairoTrace::from_file(&dir_trace).unwrap();
        let memory = CairoMemory::from_file(&dir_memory).unwrap();

        let proof_options = ProofOptions {
            blowup_factor: 2,
            fri_number_of_queries: 1,
            coset_offset: 3,
        };

        let mut cairo_air = CairoAIR::new(proof_options, &raw_trace);
        // PC FINAL AND AP FINAL are not computed correctly since they are extracted after padding to
        // power of two and therefore are zero
        cairo_air.pub_inputs.ap_final = FieldElement::zero();
        cairo_air.pub_inputs.pc_final = FieldElement::zero();

        let main_trace = CairoAIR::build_main_trace(&(raw_trace, memory));
        let mut trace_polys = main_trace.compute_trace_polys();
        let mut transcript = DefaultTranscript::new();
        let rap_challenges = CairoAIR::build_rap_challenges(&mut transcript);

        let aux_trace = CairoAIR::build_auxiliary_trace(&main_trace, &rap_challenges);
        let aux_polys = aux_trace.compute_trace_polys();

        trace_polys.extend_from_slice(&aux_polys);

        let domain = Domain::new(&cairo_air);

        assert!(validate_trace(
            &cairo_air,
            &trace_polys,
            &domain,
            &rap_challenges
        ));
    }
}
