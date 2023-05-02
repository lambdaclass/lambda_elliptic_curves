use lambdaworks_math::field::{
    element::FieldElement,
    traits::{IsTwoAdicField, RootsConfig},
};

use crate::metal::abstractions::{errors::MetalError, state::*};

use super::helpers::{self, void_ptr};
use metal::MTLSize;

use core::mem;

/// Executes parallel ordered FFT over a slice of two-adic field elements, in Metal.
/// Twiddle factors are required to be in bit-reverse order.
///
/// "Ordered" means that the input is required to be in natural order, and the output will be
/// in this order too. Natural order means that input[i] corresponds to the i-th coefficient,
/// as opposed to bit-reverse order in which input[bit_rev(i)] corresponds to the i-th
/// coefficient.
pub fn fft<F: IsTwoAdicField>(
    input: &[FieldElement<F>],
    twiddles: &[FieldElement<F>],
    state: &MetalState,
) -> Result<Vec<FieldElement<F>>, MetalError> {
    let pipeline = state.setup_pipeline("radix2_dit_butterfly")?;

    // if the input size is not a power of two, use zero padding
    let input = helpers::zero_padding(input);

    let input_buffer = state.alloc_buffer_data(&input);
    let twiddles_buffer = state.alloc_buffer_data(twiddles);
    // TODO: twiddle factors security (right now anything can be passed as twiddle factors)

    let (command_buffer, command_encoder) = state.setup_command(
        &pipeline,
        Some(&[(0, &input_buffer), (1, &twiddles_buffer)]),
    );

    let order = input.len().trailing_zeros();
    for stage in 0..order {
        let group_count = 1 << stage;
        let group_size = input.len() as u64 / group_count;

        let threadgroup_size = MTLSize::new(group_size / 2, 1, 1);
        let threadgroup_count = MTLSize::new(group_count, 1, 1);
        command_encoder.dispatch_thread_groups(threadgroup_count, threadgroup_size);
    }
    command_encoder.end_encoding();

    command_buffer.commit();
    command_buffer.wait_until_completed();

    let result = MetalState::retrieve_contents(&input_buffer);
    let result = bitrev_permutation(&result, state)?;
    Ok(result.iter().map(FieldElement::from_raw).collect())
}

/// Executes parallel ordered FFT in a bigger domain over a slice of two-adic field elements, in Metal.
///
/// "Ordered" means that the input is required to be in natural order, and the output will be
/// in this order too. Natural order means that input[i] corresponds to the i-th coefficient,
/// as opposed to bit-reverse order in which input[bit_rev(i)] corresponds to the i-th
/// coefficient.
pub fn fft_with_blowup<F: IsTwoAdicField>(
    input: &[FieldElement<F>],
    blowup_factor: usize,
    state: &MetalState,
) -> Result<Vec<FieldElement<F>>, MetalError> {
    let domain_size = (input.len() * blowup_factor).next_power_of_two();
    let order = domain_size.trailing_zeros();
    let twiddles = gen_twiddles(order.into(), RootsConfig::BitReverse, state)?;
    let mut resized = input.to_vec();
    resized.resize(domain_size, FieldElement::zero());

    fft(&resized, &twiddles, state)
}

/// Generates 2^{`order`} twiddle factors in parallel, with a certain `config`, in Metal.
pub fn gen_twiddles<F: IsTwoAdicField>(
    order: u64,
    config: RootsConfig,
    state: &MetalState,
) -> Result<Vec<FieldElement<F>>, MetalError> {
    let len = (1 << order) / 2;

    let kernel = match config {
        RootsConfig::Natural => "calc_twiddles",
        RootsConfig::NaturalInversed => "calc_twiddles_inv",
        RootsConfig::BitReverse => "calc_twiddles_bitrev",
        RootsConfig::BitReverseInversed => "calc_twiddles_bitrev_inv",
    };

    let pipeline = state.setup_pipeline(kernel)?;

    let result_buffer = state.alloc_buffer::<F::BaseType>(len);

    let (command_buffer, command_encoder) =
        state.setup_command(&pipeline, Some(&[(0, &result_buffer)]));

    let root = F::get_primitive_root_of_unity::<F>(order).unwrap();
    command_encoder.set_bytes(1, mem::size_of::<F::BaseType>() as u64, void_ptr(&root));

    let grid_size = MTLSize::new(len as u64, 1, 1);
    let threadgroup_size = MTLSize::new(pipeline.max_total_threads_per_threadgroup(), 1, 1);

    command_encoder.dispatch_threads(grid_size, threadgroup_size);
    command_encoder.end_encoding();

    command_buffer.commit();
    command_buffer.wait_until_completed();

    let result = MetalState::retrieve_contents(&result_buffer);
    Ok(result.iter().map(FieldElement::from_raw).collect())
}

/// Executes a parallel bit-reverse permutation with the elements of `input`, in Metal.
pub fn bitrev_permutation<T: Clone>(input: &[T], state: &MetalState) -> Result<Vec<T>, MetalError> {
    let pipeline = state.setup_pipeline("bitrev_permutation")?;

    let input_buffer = state.alloc_buffer_data(input);
    let result_buffer = state.alloc_buffer::<T>(input.len());

    let (command_buffer, command_encoder) =
        state.setup_command(&pipeline, Some(&[(0, &input_buffer), (1, &result_buffer)]));

    let grid_size = MTLSize::new(input.len() as u64, 1, 1);
    let threadgroup_size = MTLSize::new(pipeline.max_total_threads_per_threadgroup(), 1, 1);

    command_encoder.dispatch_threads(grid_size, threadgroup_size);
    command_encoder.end_encoding();

    command_buffer.commit();
    command_buffer.wait_until_completed();

    Ok(MetalState::retrieve_contents::<T>(&result_buffer))
}

#[cfg(test)]
mod tests {
    use crate::metal::abstractions::state::*;
    use lambdaworks_fft::roots_of_unity::get_twiddles;
    use lambdaworks_math::field::{
        fields::fft_friendly::stark_252_prime_field::Stark252PrimeField, traits::RootsConfig,
    };
    use proptest::{collection, prelude::*};

    use super::*;

    type F = Stark252PrimeField;
    type FE = FieldElement<F>;

    prop_compose! {
        fn powers_of_two(max_exp: u8)(exp in 1..max_exp) -> usize { 1 << exp }
        // max_exp cannot be multiple of the bits that represent a usize, generally 64 or 32.
        // also it can't exceed the test field's two-adicity.
    }
    prop_compose! {
        fn field_element()(num in any::<u64>().prop_filter("Avoid null polynomial", |x| x != &0)) -> FE {
            FE::from(num)
        }
    }
    prop_compose! {
        fn field_vec(max_exp: u8)(vec in collection::vec(field_element(), 2..1<<max_exp).prop_filter("Avoid polynomials of size not power of two", |vec| vec.len().is_power_of_two())) -> Vec<FE> {
            vec
        }
    }

    proptest! {
        // Property-based test that ensures Metal parallel FFT gives same result as a sequential one.
        #[test]
        fn test_metal_fft_matches_sequential(input in field_vec(6)) {
            objc::rc::autoreleasepool(|| {
                let metal_state = MetalState::new(None).unwrap();
                let order = input.len().trailing_zeros();
                let twiddles = get_twiddles(order.into(), RootsConfig::BitReverse).unwrap();

                let metal_result = super::fft(&input, &twiddles, &metal_state).unwrap();
                let sequential_result = lambdaworks_fft::ops::fft(&input).unwrap();

                prop_assert_eq!(&metal_result, &sequential_result);
                Ok(())
            }).unwrap();
        }
    }
}
