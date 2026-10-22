//! The Falcon-1024 verification equation over unpacked coefficients.
//!
//! The signer supplies mul_hint = s1 * h; two forward NTTs and a pointwise check bind it, since
//! NTT(s1) * h_ntt == NTT(mul_hint) mod q holds exactly when mul_hint is s1 * h. The norm is then
//! ||message point - mul_hint||^2 + ||s1||^2 over centered coefficients.

use pqbench_ntt::engine::ntt;
use crate::ntt::config;

/// Falcon-1024's squared norm bound (falcon.py's sig_bound for n = 1024).
pub const SIG_BOUND: u64 = 70265242;
const Q: u64 = 12289;
const HALF_Q: u64 = 6144;

/// Every span holds 1024 coefficients in [0, q).
pub fn verify_with_hint(
    s1: Span<felt252>, h_ntt: Span<felt252>, mul_hint: Span<felt252>, point: Span<felt252>,
) -> bool {
    let cfg = config();
    let s1_ntt = ntt(s1, @cfg);
    let hint_ntt = ntt(mul_hint, @cfg);
    let q: NonZero<u128> = 12289;
    let mut a = s1_ntt.span();
    let mut h = h_ntt;
    let mut t = hint_ntt.span();
    // s1n * h + q - hn is divisible by q exactly when the two NTT coordinates agree.
    while let Some(x) = a.pop_front() {
        let product: u128 = (*x * *h.pop_front().unwrap() + 12289 - *t.pop_front().unwrap())
            .try_into()
            .unwrap();
        let (_, remainder) = DivRem::div_rem(product, q);
        if remainder != 0 {
            return false;
        }
    }
    let mut norm: u64 = 0;
    let mut points = point;
    let mut hints = mul_hint;
    let mut shorts = s1;
    while let Some(p) = points.pop_front() {
        let p: u64 = (*p).try_into().unwrap();
        let k: u64 = (*hints.pop_front().unwrap()).try_into().unwrap();
        let v: u64 = (*shorts.pop_front().unwrap()).try_into().unwrap();
        let d = if p >= k {
            p - k
        } else {
            p + Q - k
        };
        norm += centered_square(d) + centered_square(v);
    }
    norm <= SIG_BOUND
}

/// x in [0, q) as its centered representative's square.
#[inline(always)]
fn centered_square(x: u64) -> u64 {
    let c = if x > HALF_Q {
        Q - x
    } else {
        x
    };
    c * c
}
