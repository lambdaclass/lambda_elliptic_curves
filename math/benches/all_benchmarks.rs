use criterion::{criterion_group, criterion_main, Criterion};

mod benchmarks;

fn run_all_benchmarks(c: &mut Criterion) {
    benchmarks::field::u64_benchmark(c);
    benchmarks::fft::ntt_benchmarks(c);
}

criterion_group!(benches, run_all_benchmarks);
criterion_main!(benches);
