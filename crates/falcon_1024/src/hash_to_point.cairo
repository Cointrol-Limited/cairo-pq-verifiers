//! The standard SHAKE-256 hash-to-point of the Falcon specification at n = 1024, as OpenZeppelin's
//! Falcon-512 crate drives it (hash_to_point_shake_512): absorb salt || message hash, then read the
//! squeezed stream as big-endian 16-bit words, keeping word % q while word < 5q, until 1024
//! coefficients. The salt is two 20-byte little-endian felts and the message hash its 32
//! little-endian bytes; the 72-byte input fits one rate block, assembled straight into lanes.

use crate::keccak::keccak_f1600;

const N: u32 = 1024;
const REJECT_BOUND: u32 = 61445;
const TWO_POW_160: u256 = 0x10000000000000000000000000000000000000000_u256;

/// The message point for (message_hash, salt), or None when a salt felt exceeds 20 bytes.
pub fn hash_to_point(
    message_hash: felt252, salt_a: felt252, salt_b: felt252,
) -> Option<Array<felt252>> {
    let sa: u256 = salt_a.into();
    let sb: u256 = salt_b.into();
    if sa >= TWO_POW_160 || sb >= TWO_POW_160 {
        return None;
    }
    let mh: u256 = message_hash.into();
    // The absorbed block as little-endian lanes: bytes 0..40 the salt, 40..72 the message hash,
    // byte 72 SHAKE's 0x1F domain byte and byte 135 the pad10*1 terminator.
    let two64: NonZero<u128> = 0x10000000000000000_u128.try_into().unwrap();
    let two32: NonZero<u128> = 0x100000000_u128.try_into().unwrap();
    let (a1, a0) = DivRem::div_rem(sa.low, two64);
    let (sbq, sb0) = DivRem::div_rem(sb.low, two32);
    let (sb12, l3) = DivRem::div_rem(sbq, two64);
    let (m1, m0) = DivRem::div_rem(mh.low, two64);
    let (m3, m2) = DivRem::div_rem(mh.high, two64);
    let l2: u128 = (sa.high.into() + sb0.into() * 0x100000000_felt252).try_into().unwrap();
    let l4: u128 = (sb12.into() + sb.high.into() * 0x100000000_felt252).try_into().unwrap();
    let mut state = keccak_f1600(
        [
            a0, a1, l2, l3, l4, m0, m1, m2, m3, 0x1f, 0, 0, 0, 0, 0, 0, 0x8000000000000000, 0, 0, 0,
            0, 0, 0, 0, 0,
        ],
    );
    let mut coeffs: Array<felt252> = array![];
    loop {
        let mut lanes = state.span().slice(0, 17);
        while let Some(lane) = lanes.pop_front() {
            lane_words(*lane, ref coeffs);
        }
        if coeffs.len() == N {
            break;
        }
        state = keccak_f1600(state);
    }
    Some(coeffs)
}

/// One squeezed lane (< 2^64) as four big-endian 16-bit words: the lane's bytes are
/// little-endian, so each 16-bit chunk b0 + 256 * b1 holds the stream word 256 * b0 + b1.
fn lane_words(lane: u128, ref coeffs: Array<felt252>) {
    let two16: NonZero<u128> = 0x10000;
    let b256: NonZero<u128> = 0x100;
    let (rest, c0) = DivRem::div_rem(lane, two16);
    let (rest, c1) = DivRem::div_rem(rest, two16);
    let (c3, c2) = DivRem::div_rem(rest, two16);
    for chunk in array![c0, c1, c2, c3] {
        let (b1, b0) = DivRem::div_rem(chunk, b256);
        let word: u32 = (b0 * 256 + b1).try_into().unwrap();
        if coeffs.len() != N && word < REJECT_BOUND {
            coeffs.append((word % 12289).into());
        }
    }
}
