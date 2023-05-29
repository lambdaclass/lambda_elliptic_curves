// https://github.com/andrewmilson/ministark/blob/main/gpu-poly/src/metal/u256.h.metal

#ifndef u256_h
#define u256_h

#include "u128.cuh"

class u256 {
public:
  u256() = default;
  __device__ constexpr u256(int l) : low(l), high(0) {}
  __device__ constexpr u256(unsigned long l) : low(u128(l)), high(0) {}
  __device__ constexpr u256(u128 l) : low(l), high(0) {}
  __device__ constexpr u256(bool b) : low(b), high(0) {}
  __device__ constexpr u256(u128 h, u128 l) : low(l), high(h) {}
  __device__ constexpr u256(unsigned long hh, unsigned long hl,
                            unsigned long lh, unsigned long ll)
      : low(u128(lh, ll)), high(u128(hh, hl)) {}

  __device__ constexpr u256 operator+(const u256 rhs) const {
    return u256(high + rhs.high + ((low + rhs.low) < low), low + rhs.low);
  }

  __device__ constexpr u256 operator+=(const u256 rhs) {
    *this = *this + rhs;
    return *this;
  }

  __device__ constexpr inline u256 operator-(const u256 rhs) const {
    return u256(high - rhs.high - ((low - rhs.low) > low), low - rhs.low);
  }

  __device__ constexpr u256 operator-=(const u256 rhs) {
    *this = *this - rhs;
    return *this;
  }

  __device__ constexpr bool operator==(const u256 rhs) const {
    return high == rhs.high && low == rhs.low;
  }

  __device__ constexpr bool operator!=(const u256 rhs) const {
    return !(*this == rhs);
  }

  __device__ constexpr bool operator<(const u256 rhs) const {
    return ((high == rhs.high) && (low < rhs.low)) || (high < rhs.high);
  }

  __device__ constexpr u256 operator&(const u256 rhs) const {
    return u256(high & rhs.high, low & rhs.low);
  }

  __device__ constexpr bool operator>(const u256 rhs) const {
    return ((high == rhs.high) && (low > rhs.low)) || (high > rhs.high);
  }

  __device__ constexpr bool operator>=(const u256 rhs) const {
    return !(*this < rhs);
  }

  __device__ constexpr bool operator<=(const u256 rhs) const {
    return !(*this > rhs);
  }

  __device__ constexpr inline u256 operator>>(unsigned shift) const {
    // TODO: reduce branch conditions
    if (shift >= 256) {
      return u256(0);
    } else if (shift == 128) {
      return u256(0, high);
    } else if (shift == 0) {
      return *this;
    } else if (shift < 128) {
      return u256(high >> shift, (high << (128 - shift)) | (low >> shift));
    } else if ((256 > shift) && (shift > 128)) {
      return u256(0, (high >> (shift - 128)));
    } else {
      return u256(0);
    }
  }

  __device__ constexpr u256 operator>>=(unsigned rhs) {
    *this = *this >> rhs;
    return *this;
  }

  __device__ u256 operator*(const bool rhs) const {
    return u256(high * rhs, low * rhs);
  }

  __device__ u256 operator*(const u256 rhs) const {
    // split values into 4 64-bit parts
    u128 top[2] = {u128(low.high), u128(low.low)};
    u128 bottom[3] = {u128(rhs.high.low), u128(rhs.low.high),
                      u128(rhs.low.low)};

    unsigned long tmp3_3 = high.high * rhs.low.low;
    unsigned long tmp0_0 = low.low * rhs.high.high;
    unsigned long tmp2_2 = high.low * rhs.low.high;

    u128 tmp2_3 = u128(high.low) * bottom[2];
    u128 tmp0_3 = top[1] * bottom[2];
    u128 tmp1_3 = top[0] * bottom[2];

    u128 tmp0_2 = top[1] * bottom[1];
    u128 third64 = u128(tmp0_2.low) + u128(tmp0_3.high);
    u128 tmp1_2 = top[0] * bottom[1];

    u128 tmp0_1 = top[1] * bottom[0];
    u128 second64 = u128(tmp0_1.low) + u128(tmp0_2.high);
    unsigned long first64 = tmp0_0 + tmp0_1.high;

    u128 tmp1_1 = top[0] * bottom[0];
    first64 += tmp1_1.low + tmp1_2.high;

    // second row
    third64 += u128(tmp1_3.low);
    second64 += u128(tmp1_2.low) + u128(tmp1_3.high);

    // third row
    second64 += u128(tmp2_3.low);
    first64 += tmp2_2 + tmp2_3.high;

    // fourth row
    first64 += tmp3_3;
    second64 += u128(third64.high);
    first64 += second64.high;

    return u256(u128(first64, second64.low), u128(third64.low, tmp0_3.low));
  }

  __device__ u256 operator*=(const u256 rhs) {
    *this = *this * rhs;
    return *this;
  }

  // TODO: Could get better performance with  smaller limb size
  // Not sure what word size is for M1 GPU
  u128 high;
  u128 low;

  // #ifdef __LITTLE_ENDIAN__
  //     u128 low;
  //     u128 high;
  // #endif
  // #ifdef __BIG_ENDIAN__

  // #endif
};

#endif /* u256_h */
