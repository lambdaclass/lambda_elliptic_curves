use lambdaworks_math::field::fields::{
    fft_friendly::stark_252_prime_field::Stark252PrimeField, u64_prime_field::FE17,
};
use lambdaworks_stark::air::example::{
    cairo, fibonacci_2_columns, fibonacci_f17, quadratic_air, simple_fibonacci,
};
use lambdaworks_stark::cairo_vm::cairo_mem::CairoMemory;
use lambdaworks_stark::cairo_vm::cairo_trace::CairoTrace;
use lambdaworks_stark::cairo_vm::execution_trace::build_cairo_execution_trace;
use lambdaworks_stark::{
    air::{
        context::{AirContext, ProofOptions},
        trace::TraceTable,
    },
    fri::FieldElement,
    prover::prove,
    verifier::verify,
};

pub type FE = FieldElement<Stark252PrimeField>;

#[test_log::test]
fn test_prove_fib() {
    let trace = simple_fibonacci::fibonacci_trace([FE::from(1), FE::from(1)], 8);
    let trace_length = trace[0].len();
    let trace_table = TraceTable::new_from_cols(&trace);

    let context = AirContext {
        options: ProofOptions {
            blowup_factor: 2,
            fri_number_of_queries: 1,
            coset_offset: 3,
        },
        trace_length,
        trace_columns: trace_table.n_cols,
        transition_degrees: vec![1],
        transition_exemptions: vec![2],
        transition_offsets: vec![0, 1, 2],
        num_transition_constraints: 1,
    };

    let fibonacci_air = simple_fibonacci::FibonacciAIR::from(context);

    let result = prove(&trace_table, &fibonacci_air);
    assert!(verify(&result, &fibonacci_air));
}

#[test_log::test]
fn test_prove_fib17() {
    let trace = simple_fibonacci::fibonacci_trace([FE17::from(1), FE17::from(1)], 4);
    let trace_table = TraceTable::new_from_cols(&trace);

    let context = AirContext {
        options: ProofOptions {
            blowup_factor: 2,
            fri_number_of_queries: 1,
            coset_offset: 3,
        },
        trace_length: trace_table.n_rows(),
        trace_columns: trace_table.n_cols,
        transition_degrees: vec![1],
        transition_exemptions: vec![2],
        transition_offsets: vec![0, 1, 2],
        num_transition_constraints: 1,
    };

    let fibonacci_air = fibonacci_f17::Fibonacci17AIR::from(context);

    let result = prove(&trace_table, &fibonacci_air);
    assert!(verify(&result, &fibonacci_air));
}

#[test_log::test]
fn test_prove_fib_2_cols() {
    let trace_columns =
        fibonacci_2_columns::fibonacci_trace_2_columns([FE::from(1), FE::from(1)], 16);

    let trace_table = TraceTable::new_from_cols(&trace_columns);

    let context = AirContext {
        options: ProofOptions {
            blowup_factor: 2,
            fri_number_of_queries: 1,
            coset_offset: 3,
        },
        trace_length: trace_table.n_rows(),
        transition_degrees: vec![1, 1],
        transition_exemptions: vec![1, 1],
        transition_offsets: vec![0, 1],
        num_transition_constraints: 2,
        trace_columns: 2,
    };

    let fibonacci_air = fibonacci_2_columns::Fibonacci2ColsAIR::from(context);

    let result = prove(&trace_table, &fibonacci_air);
    assert!(verify(&result, &fibonacci_air));
}

#[test_log::test]
fn test_prove_quadratic() {
    let trace = quadratic_air::quadratic_trace(FE::from(3), 4);
    let trace_table = TraceTable {
        table: trace.clone(),
        n_cols: 1,
    };

    let context = AirContext {
        options: ProofOptions {
            blowup_factor: 2,
            fri_number_of_queries: 1,
            coset_offset: 3,
        },
        trace_length: trace.len(),
        trace_columns: trace_table.n_cols,
        transition_degrees: vec![2],
        transition_exemptions: vec![1],
        transition_offsets: vec![0, 1],
        num_transition_constraints: 1,
    };

    let quadratic_air = quadratic_air::QuadraticAIR::from(context);

    let result = prove(&trace_table, &quadratic_air);
    assert!(verify(&result, &quadratic_air));
}

#[test_log::test]
fn test_prove_cairo_simple_program() {
    /*
    Cairo program used in the test:

    ```
    func main() {
        let x = 1;
        let y = 2;
        assert x + y = 3;
        return ();
    }

    ```
    */
    let base_dir = env!("CARGO_MANIFEST_DIR");
    let dir_trace = base_dir.to_owned() + "/src/cairo_vm/test_data/simple_program.trace";
    let dir_memory = base_dir.to_owned() + "/src/cairo_vm/test_data/simple_program.mem";

    let raw_trace = CairoTrace::from_file(&dir_trace).unwrap();
    let memory = CairoMemory::from_file(&dir_memory).unwrap();

    let execution_trace = build_cairo_execution_trace(&raw_trace, &memory);

    let proof_options = ProofOptions {
        blowup_factor: 2,
        fri_number_of_queries: 1,
        coset_offset: 3,
    };

    let cairo_air = cairo::CairoAIR::new(proof_options, &execution_trace);

    let result = prove(&execution_trace, &cairo_air);
    assert!(verify(&result, &cairo_air));
}

#[test_log::test]
fn test_prove_cairo_call_func() {
    /*
    Cairo program used in the test:

    ```
    func mul(x: felt, y: felt) -> (res: felt) {
        return (res = x * y);
    }

    func main() {
        let x = 2;
        let y = 3;

        let (res) = mul(x, y);
        assert res = 6;

        return ();
    }

    ```
    */
    let base_dir = env!("CARGO_MANIFEST_DIR");
    let dir_trace = base_dir.to_owned() + "/src/cairo_vm/test_data/call_func.trace";
    let dir_memory = base_dir.to_owned() + "/src/cairo_vm/test_data/call_func.mem";

    let raw_trace = CairoTrace::from_file(&dir_trace).unwrap();
    let memory = CairoMemory::from_file(&dir_memory).unwrap();

    let execution_trace = build_cairo_execution_trace(&raw_trace, &memory);

    let proof_options = ProofOptions {
        blowup_factor: 2,
        fri_number_of_queries: 1,
        coset_offset: 3,
    };

    let cairo_air = cairo::CairoAIR::new(proof_options, &execution_trace);

    let result = prove(&execution_trace, &cairo_air);
    assert!(verify(&result, &cairo_air));
}

#[ignore]
#[test_log::test]
fn test_prove_cairo_fibonacci() {
    let base_dir = env!("CARGO_MANIFEST_DIR");
    let dir_trace = base_dir.to_owned() + "/src/cairo_vm/test_data/fibonacci_5.trace";
    let dir_memory = base_dir.to_owned() + "/src/cairo_vm/test_data/fibonacci_5.memory";

    let raw_trace = CairoTrace::from_file(&dir_trace).expect("Cairo trace binary file not found");
    let memory = CairoMemory::from_file(&dir_memory).expect("Cairo memory binary file not found");

    let execution_trace = build_cairo_execution_trace(&raw_trace, &memory);

    let proof_options = ProofOptions {
        blowup_factor: 2,
        fri_number_of_queries: 5,
        coset_offset: 3,
    };

    let cairo_air = cairo::CairoAIR::new(proof_options, &execution_trace);

    let result = prove(&execution_trace, &cairo_air);
    assert!(verify(&result, &cairo_air));
}

#[test_log::test]
fn test_malicious_trace_does_not_verify() {
    // A valid execution trace is built from the call_func.cairo binary files.
    let base_dir = env!("CARGO_MANIFEST_DIR");
    let dir_trace = base_dir.to_owned() + "/src/cairo_vm/test_data/call_func.trace";
    let dir_memory = base_dir.to_owned() + "/src/cairo_vm/test_data/call_func.mem";

    let raw_trace = CairoTrace::from_file(&dir_trace).unwrap();
    let memory = CairoMemory::from_file(&dir_memory).unwrap();
    let execution_trace = build_cairo_execution_trace(&raw_trace, &memory);

    // Get the columns representation of the execution trace
    let mut exec_trace_cols = execution_trace.cols();
    // Get the op1 column
    let mut op1s = execution_trace.cols()[26].clone();
    // Write an arbitrary value in the first position of the op1 column.
    op1s[0] = FE::from(666);
    // Overwrite the modified op1 column into the execution trace columns representation.
    exec_trace_cols[26] = op1s;

    // Reconstruct the execution trace with this invalid op1 column.
    let reconstructed_exec_trace = TraceTable::new_from_cols(&exec_trace_cols);

    // We create the new Cairo AIR instance with the malicious trace.
    let proof_options = ProofOptions {
        blowup_factor: 2,
        fri_number_of_queries: 5,
        coset_offset: 3,
    };
    let cairo_air = cairo::CairoAIR::new(proof_options, &reconstructed_exec_trace);

    // The proof is generated and the verifier rejects the proof
    let result = prove(&reconstructed_exec_trace, &cairo_air);
    assert!(!verify(&result, &cairo_air));
}
