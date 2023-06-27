#include "./fp_u256.cuh"
#include "../fft/fft.cuh"
#include "../fft/twiddles.cuh"
#include "../fft/bitrev_permutation.cuh"
#include "../utils.h"

namespace p256
{
    // StarkWare field for Cairo
    // P =
    // 3618502788666131213697322783095070105623107215331596699973092056135872020481
    using Fp = Fp256<
        /* =N **/ /*u256(*/ 576460752303423505, 0, 0, 1 /*)*/,
        /* =R_SQUARED **/ /*u256(*/ 576413109808302096, 18446744073700081664,
        5151653887, 18446741271209837569 /*)*/,
        /* =N_PRIME **/ /*u256(*/ 576460752303423504, 18446744073709551615,
        18446744073709551615, 18446744073709551615 /*)*/
        >;
} // namespace p256

extern "C"
{
    __global__ void radix2_dit_butterfly(p256::Fp *input, const p256::Fp *twiddles)
    {
        _radix2_dit_butterfly<p256::Fp>(input, twiddles);
    }
    // NOTE: In order to calculate the inverse twiddles, call with _omega = _omega.inverse()
    __global__ void calc_twiddles(p256::Fp *result, const p256::Fp &_omega)
    {
        _calc_twiddles<p256::Fp>(result, _omega);
    };

    // NOTE: In order to calculate the inverse twiddles, call with _omega = _omega.inverse()
    __global__ void calc_twiddles_bitrev(p256::Fp *result, const p256::Fp &_omega)
    {
        _calc_twiddles_bitrev<p256::Fp>(result, _omega);
    };

    __global__ void bitrev_permutation(
        const p256::Fp *input,
        p256::Fp *result
    ) {
        _bitrev_permutation<p256::Fp>(input, result);
    };
}
