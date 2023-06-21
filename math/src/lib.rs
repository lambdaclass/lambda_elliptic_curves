#![cfg_attr(feature = "no_std", no_std)]

pub mod cyclic_group;
pub mod errors;
pub mod field;
pub mod helpers;
pub mod traits;
pub mod unsigned_integer;
// These modules don't work in no-std mode
#[cfg(not(feature = "no_std"))]
pub mod elliptic_curve;
#[cfg(not(feature = "no_std"))]
pub mod fft;
#[cfg(not(feature = "no_std"))]
pub mod msm;
#[cfg(not(feature = "no_std"))]
pub mod polynomial;
