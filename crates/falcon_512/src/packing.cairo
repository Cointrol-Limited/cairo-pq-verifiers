//! Base-Q packing of 512 Z_q coefficients into 29 felt252 slots.
//!
//! Each full slot carries two u128 halves; each half Horner-packs 9 coefficients in base
//! Q = 12289 (Q^9 < 2^128): `half = c0 + Q*(c1 + Q*(c2 + ...))`. 28 full slots hold 18
//! coefficients each; the last slot holds the remaining 8 in its low half.
//!
//! Unpacking is validating: every extracted base-Q digit is < Q by construction, and the
//! residual quotient after the last digit must be zero (each half < Q^9, the last slot
//! < Q^8). The accepted felt vectors are therefore in bijection with coefficient vectors
//! in [0, Q)^512 — no coefficient can be smuggled in a non-canonical encoding.

use corelib_imports::bounded_int::{
    AddHelper, BoundedInt, DivRemHelper, MulHelper, UnitInt, bounded_int, bounded_int_div_rem, downcast,
    upcast,
};
#[feature("bounded-int-utils")]
use core::internal::bounded_int::{ConstrainHelper, SubHelper, constrain};
use corelib_imports::integer::{U128sFromFelt252Result, u128s_from_felt252};
use pqbench_ntt::LazyCoeff;
use crate::falcon::hint_quotient_inv;
use crate::zq::Q;

/// Coefficients per full felt252 slot (two u128 halves of 9).
pub const VALS_PER_FELT: u32 = 18;
/// felt252 slots for 512 coefficients: 28 full slots + 1 slot with 8.
pub const PACKED_SLOTS: u32 = 29;
/// Coefficients in the last slot: 512 - 28*18.
const LAST_SLOT_VALS: u32 = 8;

const TWO_POW_128: felt252 = 0x100000000000000000000000000000000;

pub(crate) type PackingZq = BoundedInt<0, 12288>;
type PackingQ = UnitInt<12289>;
type Acc1 = BoundedInt<0, 151019520>;
type Acc2 = BoundedInt<0, 1855878893568>;
type Acc3 = BoundedInt<0, 22806895723069440>;
type Acc4 = BoundedInt<0, 280273941540800360448>;
type Acc5 = BoundedInt<0, 3444286467594895629557760>;
type Acc6 = BoundedInt<0, 42326836400273672391635324928>;
type Acc7 = BoundedInt<0, 520154492522963160020806508052480>;
type Acc8 = BoundedInt<0, 6392178558614694273495691177456939008>;

const PACKING_Q_NZ: NonZero<PackingQ> = 12289;

/// The divisor as a cell rather than an immediate: inside the unpacking loop it is a loop
/// parameter, so each division uses it in place instead of first copying the constant.
#[inline(never)]
fn packing_q_cell() -> NonZero<PackingQ> {
    PACKING_Q_NZ
}

impl PackingDivRemAcc1Impl of DivRemHelper<Acc1, PackingQ> {
    type DivT = PackingZq;
    type RemT = PackingZq;
}

impl PackingDivRemAcc2Impl of DivRemHelper<Acc2, PackingQ> {
    type DivT = Acc1;
    type RemT = PackingZq;
}

impl PackingDivRemAcc3Impl of DivRemHelper<Acc3, PackingQ> {
    type DivT = Acc2;
    type RemT = PackingZq;
}

impl PackingDivRemAcc4Impl of DivRemHelper<Acc4, PackingQ> {
    type DivT = Acc3;
    type RemT = PackingZq;
}

impl PackingDivRemAcc5Impl of DivRemHelper<Acc5, PackingQ> {
    type DivT = Acc4;
    type RemT = PackingZq;
}

impl PackingDivRemAcc6Impl of DivRemHelper<Acc6, PackingQ> {
    type DivT = Acc5;
    type RemT = PackingZq;
}

impl PackingDivRemAcc7Impl of DivRemHelper<Acc7, PackingQ> {
    type DivT = Acc6;
    type RemT = PackingZq;
}

impl PackingDivRemAcc8Impl of DivRemHelper<Acc8, PackingQ> {
    type DivT = Acc7;
    type RemT = PackingZq;
}

/// Unpack 29 packed felts into 512 coefficients in [0, Q), as felts (each is a
/// base-Q digit, so the range holds by construction).
/// Returns `None` on wrong length or any non-canonical slot encoding.
pub fn unpack_512(packed: Span<felt252>) -> Option<Array<felt252>> {
    let coeffs_u16 = match unpack_512_u16(packed) {
        Some(v) => v,
        None => { return None; },
    };
    let mut coeffs_u16 = coeffs_u16.span();
    let mut coeffs: Array<felt252> = array![];
    while let Some(coeff) = coeffs_u16.pop_front() {
        coeffs.append((*coeff).into());
    }
    Some(coeffs)
}

/// Unpack the canonical 29-slot encoding directly into the verifier's `u16` form.
/// Returns `None` on wrong length or any non-canonical slot encoding.
pub(crate) fn unpack_512_u16(packed: Span<felt252>) -> Option<Array<u16>> {
    if packed.len() != PACKED_SLOTS {
        return None;
    }
    let mut coeffs: Array<u16> = array![];
    let q = packing_q_cell();
    let mut full_slots = packed.slice(0, PACKED_SLOTS - 1);
    while let Some(chunk) = full_slots.multi_pop_front::<7>() {
        let [f0, f1, f2, f3, f4, f5, f6] = (*chunk).unbox();
        if !unpack_full_slot_u16(f0, ref coeffs, q)
            || !unpack_full_slot_u16(f1, ref coeffs, q)
            || !unpack_full_slot_u16(f2, ref coeffs, q)
            || !unpack_full_slot_u16(f3, ref coeffs, q)
            || !unpack_full_slot_u16(f4, ref coeffs, q)
            || !unpack_full_slot_u16(f5, ref coeffs, q)
            || !unpack_full_slot_u16(f6, ref coeffs, q) {
            return None;
        }
    }
    let last: u256 = (*packed.at(PACKED_SLOTS - 1)).into();
    if last.high != 0 || !unpack_half8_u16(last.low, ref coeffs, q) {
        return None;
    }
    Some(coeffs)
}

#[inline(always)]
fn unpack_full_slot_u16(felt: felt252, ref coeffs: Array<u16>, q: NonZero<PackingQ>) -> bool {
    let value: u256 = felt.into();
    unpack_half9_u16(value.low, ref coeffs, q) && unpack_half9_u16(value.high, ref coeffs, q)
}

/// Extract nine base-Q digits from a u128 half. Values below Q^9 are canonical;
/// after eight divisions the remaining quotient is the ninth digit.
#[inline(always)]
fn unpack_half9_u16(value: u128, ref coeffs: Array<u16>, q: NonZero<PackingQ>) -> bool {
    let value: Acc8 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
    let (rest, d0) = bounded_int_div_rem(value, q);
    let (rest, d1) = bounded_int_div_rem(rest, q);
    let (rest, d2) = bounded_int_div_rem(rest, q);
    let (rest, d3) = bounded_int_div_rem(rest, q);
    let (rest, d4) = bounded_int_div_rem(rest, q);
    let (rest, d5) = bounded_int_div_rem(rest, q);
    let (rest, d6) = bounded_int_div_rem(rest, q);
    let (rest, d7) = bounded_int_div_rem(rest, q);
    coeffs.append(upcast(d0));
    coeffs.append(upcast(d1));
    coeffs.append(upcast(d2));
    coeffs.append(upcast(d3));
    coeffs.append(upcast(d4));
    coeffs.append(upcast(d5));
    coeffs.append(upcast(d6));
    coeffs.append(upcast(d7));
    coeffs.append(upcast(rest));
    true
}

/// Extract the final slot's eight digits after checking the value is below Q^8.
#[inline(always)]
fn unpack_half8_u16(value: u128, ref coeffs: Array<u16>, q: NonZero<PackingQ>) -> bool {
    let value: Acc7 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
    let (rest, d0) = bounded_int_div_rem(value, q);
    let (rest, d1) = bounded_int_div_rem(rest, q);
    let (rest, d2) = bounded_int_div_rem(rest, q);
    let (rest, d3) = bounded_int_div_rem(rest, q);
    let (rest, d4) = bounded_int_div_rem(rest, q);
    let (rest, d5) = bounded_int_div_rem(rest, q);
    let (rest, d6) = bounded_int_div_rem(rest, q);
    coeffs.append(upcast(d0));
    coeffs.append(upcast(d1));
    coeffs.append(upcast(d2));
    coeffs.append(upcast(d3));
    coeffs.append(upcast(d4));
    coeffs.append(upcast(d5));
    coeffs.append(upcast(d6));
    coeffs.append(upcast(rest));
    true
}

/// Pack 512 coefficients (each < Q) into 29 felts. Inverse of [`unpack_512`];
/// used by tests and off-chain tooling mirrors. Panics on bad length or coefficient.
pub fn pack_512(coeffs: Span<u16>) -> Array<felt252> {
    assert(coeffs.len() == 512, 'pack: need 512 coeffs');
    let mut packed: Array<felt252> = array![];
    let mut slot: u32 = 0;
    while slot != PACKED_SLOTS - 1 {
        let low = pack_half(coeffs.slice(slot * VALS_PER_FELT, 9));
        let high = pack_half(coeffs.slice(slot * VALS_PER_FELT + 9, 9));
        packed.append(low.into() + high.into() * TWO_POW_128);
        slot += 1;
    }
    packed.append(pack_half(coeffs.slice(504, LAST_SLOT_VALS)).into());
    packed
}

/// Horner-encode up to 9 coefficients into a u128: c0 + Q*(c1 + Q*(c2 + ...)).
fn pack_half(coeffs: Span<u16>) -> u128 {
    let mut acc: u128 = 0;
    let mut i = coeffs.len();
    while i != 0 {
        i -= 1;
        let c = *coeffs.at(i);
        assert(c < Q, 'pack: coeff >= Q');
        acc = acc * 12289 + c.into();
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::{PACKED_SLOTS, pack_512, unpack_512, unpack_512_u16};

    /// Q^9: the smallest non-canonical low-half value (all 9 digits zero, residue 1).
    const Q_POW_9: felt252 = 6392178558614694273495691177456939009;
    /// Q^8: the smallest non-canonical last-slot value.
    const Q_POW_8: felt252 = 520154492522963160020806508052481;
    const TWO_POW_128: felt252 = 0x100000000000000000000000000000000;

    fn pseudorandom_coeffs() -> Array<u16> {
        let mut f: Array<u16> = array![];
        let mut state: u64 = 7;
        for _ in 0_u32..512 {
            state = (state * 1664525 + 1013904223) % 0x100000000;
            f.append((state % 12289).try_into().unwrap());
        }
        f
    }

    fn as_felts(mut vals: Span<u16>) -> Array<felt252> {
        let mut out: Array<felt252> = array![];
        while let Some(v) = vals.pop_front() {
            out.append((*v).into());
        }
        out
    }

    #[test]
    fn test_pack_unpack_roundtrip() {
        let coeffs = pseudorandom_coeffs();
        let packed = pack_512(coeffs.span());
        assert_eq!(packed.len(), PACKED_SLOTS);
        let unpacked = unpack_512(packed.span()).unwrap();
        assert_eq!(unpacked.span(), as_felts(coeffs.span()).span());
        assert_eq!(unpack_512_u16(packed.span()).unwrap().span(), coeffs.span());
    }

    #[test]
    fn test_unpack_all_zero_and_max() {
        let mut zeros: Array<u16> = array![];
        let mut maxed: Array<u16> = array![];
        for _ in 0_u32..512 {
            zeros.append(0);
            maxed.append(12288);
        }
        let z = unpack_512(pack_512(zeros.span()).span()).unwrap();
        assert_eq!(z.span(), as_felts(zeros.span()).span());
        let m = unpack_512(pack_512(maxed.span()).span()).unwrap();
        assert_eq!(m.span(), as_felts(maxed.span()).span());
    }

    #[test]
    fn test_unpack_rejects_wrong_length() {
        let coeffs = pseudorandom_coeffs();
        let packed = pack_512(coeffs.span());
        assert!(unpack_512(packed.span().slice(0, 28)).is_none());
        assert!(unpack_512(array![].span()).is_none());
    }

    #[test]
    fn test_unpack_rejects_noncanonical_half() {
        // Q^9 in a low half: nine zero digits with a nonzero residue.
        let mut packed = pack_512(pseudorandom_coeffs().span());
        let mut tampered: Array<felt252> = array![Q_POW_9];
        let mut rest = packed.span().slice(1, 28);
        while let Some(f) = rest.pop_front() {
            tampered.append(*f);
        }
        assert!(unpack_512(tampered.span()).is_none());
        // Same overflow in a high half.
        let mut tampered2: Array<felt252> = array![Q_POW_9 * TWO_POW_128];
        let mut rest2 = packed.span().slice(1, 28);
        while let Some(f) = rest2.pop_front() {
            tampered2.append(*f);
        }
        assert!(unpack_512(tampered2.span()).is_none());
    }

    #[test]
    fn test_unpack_rejects_noncanonical_last_slot() {
        let packed = pack_512(pseudorandom_coeffs().span());
        // Non-zero high half in the last slot.
        let mut tampered: Array<felt252> = array![];
        let mut head = packed.span().slice(0, 28);
        while let Some(f) = head.pop_front() {
            tampered.append(*f);
        }
        tampered.append(TWO_POW_128);
        assert!(unpack_512(tampered.span()).is_none());
        // Q^8 in the last slot: eight zero digits with a nonzero residue.
        let mut tampered2: Array<felt252> = array![];
        let mut head2 = packed.span().slice(0, 28);
        while let Some(f) = head2.pop_front() {
            tampered2.append(*f);
        }
        tampered2.append(Q_POW_8);
        assert!(unpack_512(tampered2.span()).is_none());
    }
}


#[inline(always)]
fn unpack_full_slot_zq(felt: felt252, ref coeffs: Array<PackingZq>, q: NonZero<PackingQ>) -> bool {
    let value: u256 = felt.into();
    unpack_half9_zq(value.low, ref coeffs, q) && unpack_half9_zq(value.high, ref coeffs, q)
}

/// Extract nine base-Q digits from a u128 half. Values below Q^9 are canonical;
/// after eight divisions the remaining quotient is the ninth digit.
#[inline(always)]
fn unpack_half9_zq(value: u128, ref coeffs: Array<PackingZq>, q: NonZero<PackingQ>) -> bool {
    let value: Acc8 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
    let (rest, d0) = bounded_int_div_rem(value, q);
    let (rest, d1) = bounded_int_div_rem(rest, q);
    let (rest, d2) = bounded_int_div_rem(rest, q);
    let (rest, d3) = bounded_int_div_rem(rest, q);
    let (rest, d4) = bounded_int_div_rem(rest, q);
    let (rest, d5) = bounded_int_div_rem(rest, q);
    let (rest, d6) = bounded_int_div_rem(rest, q);
    let (rest, d7) = bounded_int_div_rem(rest, q);
    coeffs.append(d0);
    coeffs.append(d1);
    coeffs.append(d2);
    coeffs.append(d3);
    coeffs.append(d4);
    coeffs.append(d5);
    coeffs.append(d6);
    coeffs.append(d7);
    coeffs.append(rest);
    true
}

/// Extract the final slot's eight digits after checking the value is below Q^8.
#[inline(always)]
fn unpack_half8_zq(value: u128, ref coeffs: Array<PackingZq>, q: NonZero<PackingQ>) -> bool {
    let value: Acc7 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
    let (rest, d0) = bounded_int_div_rem(value, q);
    let (rest, d1) = bounded_int_div_rem(rest, q);
    let (rest, d2) = bounded_int_div_rem(rest, q);
    let (rest, d3) = bounded_int_div_rem(rest, q);
    let (rest, d4) = bounded_int_div_rem(rest, q);
    let (rest, d5) = bounded_int_div_rem(rest, q);
    let (rest, d6) = bounded_int_div_rem(rest, q);
    coeffs.append(d0);
    coeffs.append(d1);
    coeffs.append(d2);
    coeffs.append(d3);
    coeffs.append(d4);
    coeffs.append(d5);
    coeffs.append(d6);
    coeffs.append(rest);
    true
}

type CenterShiftZq = BoundedInt<6144, 18432>;
type CenteredZq = BoundedInt<-6144, 6144>;
impl AddZqHalf of AddHelper<PackingZq, UnitInt<6144>> {
    type Result = CenterShiftZq;
}
impl DivRemCenterShiftZq of DivRemHelper<CenterShiftZq, PackingQ> {
    type DivT = BoundedInt<0, 1>;
    type RemT = PackingZq;
}
impl SubZqHalf of SubHelper<PackingZq, UnitInt<6144>> {
    type Result = CenteredZq;
}
impl MulCenteredZq of MulHelper<CenteredZq, CenteredZq> {
    type Result = BoundedInt<-37748736, 37748736>;
}

/// The centered square of a digit: `(d + 6144) mod q - 6144` lies in [-6144, 6144] and is
/// congruent to `d`.
impl ConstrainZqHalf of ConstrainHelper<PackingZq, 6145> {
    type LowT = BoundedInt<0, 6144>;
    type HighT = BoundedInt<6145, 12288>;
}

#[inline(always)]
fn center_sq_zq(d: PackingZq, q: NonZero<PackingQ>) -> felt252 {
    // One range check: d <= 6144 is its own centered value, otherwise d - q is.
    let x: felt252 = match constrain::<PackingZq, 6145>(d) {
        Ok(low) => low.into(),
        Err(high) => high.into() - 12289,
    };
    x * x
}

type DiffShiftZq = BoundedInt<6145, 83968>;
impl AddU16DiffOffset of AddHelper<u16, UnitInt<18433>> {
    type Result = BoundedInt<18433, 83968>;
}
impl SubDiffZq of SubHelper<BoundedInt<18433, 83968>, PackingZq> {
    type Result = DiffShiftZq;
}
impl DivRemDiffShiftZq of DivRemHelper<DiffShiftZq, PackingQ> {
    type DivT = BoundedInt<0, 6>;
    type RemT = PackingZq;
}

/// The centered square of `m - t` mod q: `(m + 6144 + q - t) mod q - 6144` lies in
/// [-6144, 6144] and is congruent to `m - t`.
#[inline(always)]
fn center_diff_sq_zq(m: u16, t: PackingZq, q: NonZero<PackingQ>) -> felt252 {
    let offset: UnitInt<18433> = 18433;
    let half: UnitInt<6144> = 6144;
    let (_, r) = bounded_int_div_rem(bounded_int::sub(bounded_int::add(m, offset), t), q);
    let c = bounded_int::sub(r, half);
    bounded_int::mul(c, c).into()
}

/// Q57: two digits centred by one constrain tree (4 leaves) and merged once, so the
/// range-check pointer store and the branch jump are paid per pair, not per digit. Same
/// centered values as two `center_sq_zq` calls.
#[inline(always)]
fn center_pair_zq(a: PackingZq, b: PackingZq) -> (felt252, felt252) {
    match constrain::<PackingZq, 6145>(a) {
        Ok(la) => match constrain::<PackingZq, 6145>(b) {
            Ok(lb) => (la.into(), lb.into()),
            Err(hb) => (la.into(), hb.into() - 12289),
        },
        Err(ha) => match constrain::<PackingZq, 6145>(b) {
            Ok(lb) => (ha.into() - 12289, lb.into()),
            Err(hb) => (ha.into() - 12289, hb.into() - 12289),
        },
    }
}

// Q21 BEGIN (generated by data/artifacts/q21/gen_q21.py)


#[inline(always)]
fn digits9_np8(value: Acc8, ref norm: felt252, q: NonZero<PackingQ>) -> (felt252, felt252, felt252, felt252, felt252, felt252, felt252, felt252, PackingZq) {
    let (rest, d0) = bounded_int_div_rem(value, q);
    let (rest, d1) = bounded_int_div_rem(rest, q);
    let (rest, d2) = bounded_int_div_rem(rest, q);
    let (rest, d3) = bounded_int_div_rem(rest, q);
    let (rest, d4) = bounded_int_div_rem(rest, q);
    let (rest, d5) = bounded_int_div_rem(rest, q);
    let (rest, d6) = bounded_int_div_rem(rest, q);
    let (rest, d7) = bounded_int_div_rem(rest, q);
    let (a, b) = center_pair_zq(d0, d1);
    norm += a * a;
    norm += b * b;
    let (a, b) = center_pair_zq(d2, d3);
    norm += a * a;
    norm += b * b;
    let (a, b) = center_pair_zq(d4, d5);
    norm += a * a;
    norm += b * b;
    let (a, b) = center_pair_zq(d6, d7);
    norm += a * a;
    norm += b * b;
    (d0.into(), d1.into(), d2.into(), d3.into(), d4.into(), d5.into(), d6.into(), d7.into(), rest)
}

#[inline(always)]
fn digits9_d(value: Acc8, m: [u16; 9], ref norm: felt252, q: NonZero<PackingQ>) -> (felt252, felt252, felt252, felt252, felt252, felt252, felt252, felt252, felt252) {
    let (rest, d0) = bounded_int_div_rem(value, q);
    let (rest, d1) = bounded_int_div_rem(rest, q);
    let (rest, d2) = bounded_int_div_rem(rest, q);
    let (rest, d3) = bounded_int_div_rem(rest, q);
    let (rest, d4) = bounded_int_div_rem(rest, q);
    let (rest, d5) = bounded_int_div_rem(rest, q);
    let (rest, d6) = bounded_int_div_rem(rest, q);
    let (rest, d7) = bounded_int_div_rem(rest, q);
    let [m0, m1, m2, m3, m4, m5, m6, m7, m8] = m;
    norm += center_diff_sq_zq(m0, d0, q);
    norm += center_diff_sq_zq(m1, d1, q);
    norm += center_diff_sq_zq(m2, d2, q);
    norm += center_diff_sq_zq(m3, d3, q);
    norm += center_diff_sq_zq(m4, d4, q);
    norm += center_diff_sq_zq(m5, d5, q);
    norm += center_diff_sq_zq(m6, d6, q);
    norm += center_diff_sq_zq(m7, d7, q);
    norm += center_diff_sq_zq(m8, rest, q);
    (d0.into(), d1.into(), d2.into(), d3.into(), d4.into(), d5.into(), d6.into(), d7.into(), rest.into())
}


#[inline(always)]
fn digits8_np(value: Acc7, ref norm: felt252, q: NonZero<PackingQ>) -> (felt252, felt252, felt252, felt252, felt252, felt252, felt252, felt252) {
    let (rest, d0) = bounded_int_div_rem(value, q);
    let (rest, d1) = bounded_int_div_rem(rest, q);
    let (rest, d2) = bounded_int_div_rem(rest, q);
    let (rest, d3) = bounded_int_div_rem(rest, q);
    let (rest, d4) = bounded_int_div_rem(rest, q);
    let (rest, d5) = bounded_int_div_rem(rest, q);
    let (rest, d6) = bounded_int_div_rem(rest, q);
    let (a, b) = center_pair_zq(d0, d1);
    norm += a * a;
    norm += b * b;
    let (a, b) = center_pair_zq(d2, d3);
    norm += a * a;
    norm += b * b;
    let (a, b) = center_pair_zq(d4, d5);
    norm += a * a;
    norm += b * b;
    let (a, b) = center_pair_zq(d6, rest);
    norm += a * a;
    norm += b * b;
    (d0.into(), d1.into(), d2.into(), d3.into(), d4.into(), d5.into(), d6.into(), rest.into())
}

#[inline(always)]
fn digits8_d(value: Acc7, m: [u16; 8], ref norm: felt252, q: NonZero<PackingQ>) -> (felt252, felt252, felt252, felt252, felt252, felt252, felt252, felt252) {
    let (rest, d0) = bounded_int_div_rem(value, q);
    let (rest, d1) = bounded_int_div_rem(rest, q);
    let (rest, d2) = bounded_int_div_rem(rest, q);
    let (rest, d3) = bounded_int_div_rem(rest, q);
    let (rest, d4) = bounded_int_div_rem(rest, q);
    let (rest, d5) = bounded_int_div_rem(rest, q);
    let (rest, d6) = bounded_int_div_rem(rest, q);
    let [m0, m1, m2, m3, m4, m5, m6, m7] = m;
    norm += center_diff_sq_zq(m0, d0, q);
    norm += center_diff_sq_zq(m1, d1, q);
    norm += center_diff_sq_zq(m2, d2, q);
    norm += center_diff_sq_zq(m3, d3, q);
    norm += center_diff_sq_zq(m4, d4, q);
    norm += center_diff_sq_zq(m5, d5, q);
    norm += center_diff_sq_zq(m6, d6, q);
    norm += center_diff_sq_zq(m7, rest, q);
    (d0.into(), d1.into(), d2.into(), d3.into(), d4.into(), d5.into(), d6.into(), rest.into())
}

#[inline(never)]
/// All-zero digits for a rejected chunk (its verdict is carried by the flag).
const ZERO72: [felt252; 72] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

fn unpack_chunk_ntt_d4(
    f0: felt252, f1: felt252, f2: felt252, f3: felt252, ref msg: Span<u16>, ref norm: felt252, q: NonZero<PackingQ>, s: felt252,
) -> ([felt252; 72], bool) {
    let [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69, m70, m71] = match msg.multi_pop_front::<72>() {
        Some(b) => (*b).unbox(),
        None => { return (ZERO72, false); },
    };
    let (high, low) = match u128s_from_felt252(f0) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO72, false); },
    };
    let (x0, x1, x2, x3, x4, x5, x6, x7, x8) = digits9_d(half, [m0, m1, m2, m3, m4, m5, m6, m7, m8], ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO72, false); },
    };
    let (x9, x10, x11, x12, x13, x14, x15, x16, x17) = digits9_d(half, [m9, m10, m11, m12, m13, m14, m15, m16, m17], ref norm, q);
    let (high, low) = match u128s_from_felt252(f1) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO72, false); },
    };
    let (x18, x19, x20, x21, x22, x23, x24, x25, x26) = digits9_d(half, [m18, m19, m20, m21, m22, m23, m24, m25, m26], ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO72, false); },
    };
    let (x27, x28, x29, x30, x31, x32, x33, x34, x35) = digits9_d(half, [m27, m28, m29, m30, m31, m32, m33, m34, m35], ref norm, q);
    let (high, low) = match u128s_from_felt252(f2) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO72, false); },
    };
    let (x36, x37, x38, x39, x40, x41, x42, x43, x44) = digits9_d(half, [m36, m37, m38, m39, m40, m41, m42, m43, m44], ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO72, false); },
    };
    let (x45, x46, x47, x48, x49, x50, x51, x52, x53) = digits9_d(half, [m45, m46, m47, m48, m49, m50, m51, m52, m53], ref norm, q);
    let (high, low) = match u128s_from_felt252(f3) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO72, false); },
    };
    let (x54, x55, x56, x57, x58, x59, x60, x61, x62) = digits9_d(half, [m54, m55, m56, m57, m58, m59, m60, m61, m62], ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO72, false); },
    };
    let (x63, x64, x65, x66, x67, x68, x69, x70, x71) = digits9_d(half, [m63, m64, m65, m66, m67, m68, m69, m70, m71], ref norm, q);
    ([x0 * s, x1 * s, x2 * s, x3 * s, x4 * s, x5 * s, x6 * s, x7 * s, x8 * s, x9 * s, x10 * s, x11 * s, x12 * s, x13 * s, x14 * s, x15 * s, x16 * s, x17 * s, x18 * s, x19 * s, x20 * s, x21 * s, x22 * s, x23 * s, x24 * s, x25 * s, x26 * s, x27 * s, x28 * s, x29 * s, x30 * s, x31 * s, x32 * s, x33 * s, x34 * s, x35 * s, x36 * s, x37 * s, x38 * s, x39 * s, x40 * s, x41 * s, x42 * s, x43 * s, x44 * s, x45 * s, x46 * s, x47 * s, x48 * s, x49 * s, x50 * s, x51 * s, x52 * s, x53 * s, x54 * s, x55 * s, x56 * s, x57 * s, x58 * s, x59 * s, x60 * s, x61 * s, x62 * s, x63 * s, x64 * s, x65 * s, x66 * s, x67 * s, x68 * s, x69 * s, x70 * s, x71 * s], true)
}
/// Q45: chunk readers of other sizes for the unpack schedules above (same per-slot code).
#[inline(never)]
/// Digits come back multiplied by `s`: 1, or the transform's first-layer twiddle 1479 for a
/// chunk whose coefficients are its inputs 256..511 (see `ntt_falcon512_fast_inner`).
fn unpack_chunk_ntt_n4(
    f0: felt252, f1: felt252, f2: felt252, f3: felt252, ref norm: felt252, q: NonZero<PackingQ>, s: felt252,
) -> Option<[felt252; 72]> {
    let (high, low) = match u128s_from_felt252(f0) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x0, x1, x2, x3, x4, x5, x6, x7, r_x8) = digits9_np8(half, ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x9, x10, x11, x12, x13, x14, x15, x16, r_x17) = digits9_np8(half, ref norm, q);
    let (a, b) = center_pair_zq(r_x8, r_x17);
    norm += a * a;
    norm += b * b;
    let x8: felt252 = r_x8.into();
    let x17: felt252 = r_x17.into();
    let (high, low) = match u128s_from_felt252(f1) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x18, x19, x20, x21, x22, x23, x24, x25, r_x26) = digits9_np8(half, ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x27, x28, x29, x30, x31, x32, x33, x34, r_x35) = digits9_np8(half, ref norm, q);
    let (a, b) = center_pair_zq(r_x26, r_x35);
    norm += a * a;
    norm += b * b;
    let x26: felt252 = r_x26.into();
    let x35: felt252 = r_x35.into();
    let (high, low) = match u128s_from_felt252(f2) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x36, x37, x38, x39, x40, x41, x42, x43, r_x44) = digits9_np8(half, ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x45, x46, x47, x48, x49, x50, x51, x52, r_x53) = digits9_np8(half, ref norm, q);
    let (a, b) = center_pair_zq(r_x44, r_x53);
    norm += a * a;
    norm += b * b;
    let x44: felt252 = r_x44.into();
    let x53: felt252 = r_x53.into();
    let (high, low) = match u128s_from_felt252(f3) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x54, x55, x56, x57, x58, x59, x60, x61, r_x62) = digits9_np8(half, ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x63, x64, x65, x66, x67, x68, x69, x70, r_x71) = digits9_np8(half, ref norm, q);
    let (a, b) = center_pair_zq(r_x62, r_x71);
    norm += a * a;
    norm += b * b;
    let x62: felt252 = r_x62.into();
    let x71: felt252 = r_x71.into();
    Some([x0 * s, x1 * s, x2 * s, x3 * s, x4 * s, x5 * s, x6 * s, x7 * s, x8 * s, x9 * s, x10 * s, x11 * s, x12 * s, x13 * s, x14 * s, x15 * s, x16 * s, x17 * s, x18 * s, x19 * s, x20 * s, x21 * s, x22 * s, x23 * s, x24 * s, x25 * s, x26 * s, x27 * s, x28 * s, x29 * s, x30 * s, x31 * s, x32 * s, x33 * s, x34 * s, x35 * s, x36 * s, x37 * s, x38 * s, x39 * s, x40 * s, x41 * s, x42 * s, x43 * s, x44 * s, x45 * s, x46 * s, x47 * s, x48 * s, x49 * s, x50 * s, x51 * s, x52 * s, x53 * s, x54 * s, x55 * s, x56 * s, x57 * s, x58 * s, x59 * s, x60 * s, x61 * s, x62 * s, x63 * s, x64 * s, x65 * s, x66 * s, x67 * s, x68 * s, x69 * s, x70 * s, x71 * s])
}

#[inline(always)]
fn unpack_chunk_ntt_n4_inl(
    f0: felt252, f1: felt252, f2: felt252, f3: felt252, ref norm: felt252, q: NonZero<PackingQ>, s: felt252,
) -> Option<[felt252; 72]> {
    let (high, low) = match u128s_from_felt252(f0) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x0, x1, x2, x3, x4, x5, x6, x7, r_x8) = digits9_np8(half, ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x9, x10, x11, x12, x13, x14, x15, x16, r_x17) = digits9_np8(half, ref norm, q);
    let (a, b) = center_pair_zq(r_x8, r_x17);
    norm += a * a;
    norm += b * b;
    let x8: felt252 = r_x8.into();
    let x17: felt252 = r_x17.into();
    let (high, low) = match u128s_from_felt252(f1) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x18, x19, x20, x21, x22, x23, x24, x25, r_x26) = digits9_np8(half, ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x27, x28, x29, x30, x31, x32, x33, x34, r_x35) = digits9_np8(half, ref norm, q);
    let (a, b) = center_pair_zq(r_x26, r_x35);
    norm += a * a;
    norm += b * b;
    let x26: felt252 = r_x26.into();
    let x35: felt252 = r_x35.into();
    let (high, low) = match u128s_from_felt252(f2) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x36, x37, x38, x39, x40, x41, x42, x43, r_x44) = digits9_np8(half, ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x45, x46, x47, x48, x49, x50, x51, x52, r_x53) = digits9_np8(half, ref norm, q);
    let (a, b) = center_pair_zq(r_x44, r_x53);
    norm += a * a;
    norm += b * b;
    let x44: felt252 = r_x44.into();
    let x53: felt252 = r_x53.into();
    let (high, low) = match u128s_from_felt252(f3) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x54, x55, x56, x57, x58, x59, x60, x61, r_x62) = digits9_np8(half, ref norm, q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x63, x64, x65, x66, x67, x68, x69, x70, r_x71) = digits9_np8(half, ref norm, q);
    let (a, b) = center_pair_zq(r_x62, r_x71);
    norm += a * a;
    norm += b * b;
    let x62: felt252 = r_x62.into();
    let x71: felt252 = r_x71.into();
    Some([x0 * s, x1 * s, x2 * s, x3 * s, x4 * s, x5 * s, x6 * s, x7 * s, x8 * s, x9 * s, x10 * s, x11 * s, x12 * s, x13 * s, x14 * s, x15 * s, x16 * s, x17 * s, x18 * s, x19 * s, x20 * s, x21 * s, x22 * s, x23 * s, x24 * s, x25 * s, x26 * s, x27 * s, x28 * s, x29 * s, x30 * s, x31 * s, x32 * s, x33 * s, x34 * s, x35 * s, x36 * s, x37 * s, x38 * s, x39 * s, x40 * s, x41 * s, x42 * s, x43 * s, x44 * s, x45 * s, x46 * s, x47 * s, x48 * s, x49 * s, x50 * s, x51 * s, x52 * s, x53 * s, x54 * s, x55 * s, x56 * s, x57 * s, x58 * s, x59 * s, x60 * s, x61 * s, x62 * s, x63 * s, x64 * s, x65 * s, x66 * s, x67 * s, x68 * s, x69 * s, x70 * s, x71 * s])
}

// Q21 END

/// Zero as a seven-digit accumulator, for the reject path of the hint's last slot.
const ZERO_ACC7: Acc7 = 0;

/// One public-key slot against the two transforms, out of line: [`verify_tail`] passes the
/// slot's 18 coordinates of each transform as arguments (the transforms stay on its stack).
/// Same digits and checks as one slot of [`unpack_512_zq_check`].
#[inline(never)]
fn check_slot_zq(felt: felt252, a: [LazyCoeff; 18], c: [LazyCoeff; 18], q: NonZero<PackingQ>) -> bool {
    let [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17] = a;
    let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17] = c;
    let (high, low) = match u128s_from_felt252(felt) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0, x),
    };
    check_half9_zq(low, [a0, a1, a2, a3, a4, a5, a6, a7, a8], [c0, c1, c2, c3, c4, c5, c6, c7, c8], q)
        && check_half9_zq(high, [a9, a10, a11, a12, a13, a14, a15, a16, a17], [c9, c10, c11, c12, c13, c14, c15, c16, c17], q)
}

#[inline(always)]
fn check_half9_zq(value: u128, a: [LazyCoeff; 9], c: [LazyCoeff; 9], q: NonZero<PackingQ>) -> bool {
    let [a0, a1, a2, a3, a4, a5, a6, a7, a8] = a;
    let [c0, c1, c2, c3, c4, c5, c6, c7, c8] = c;
    let x: Acc8 = match downcast(value) {
        Some(x) => x,
        None => { return false; },
    };
    let (x, d0) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a0, d0, c0)) {
        return false;
    }
    let (x, d1) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a1, d1, c1)) {
        return false;
    }
    let (x, d2) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a2, d2, c2)) {
        return false;
    }
    let (x, d3) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a3, d3, c3)) {
        return false;
    }
    let (x, d4) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a4, d4, c4)) {
        return false;
    }
    let (x, d5) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a5, d5, c5)) {
        return false;
    }
    let (x, d6) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a6, d6, c6)) {
        return false;
    }
    let (x, d7) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a7, d7, c7)) {
        return false;
    }
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a8, x, c8)) {
        return false;
    }
    true
}

/// The key's last slot (eight coordinates) against the two transforms.
#[inline(never)]
fn check_last_slot_zq(felt: felt252, a: [LazyCoeff; 8], c: [LazyCoeff; 8], q: NonZero<PackingQ>) -> bool {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [c0, c1, c2, c3, c4, c5, c6, c7] = c;
    let low = match u128s_from_felt252(felt) {
        U128sFromFelt252Result::Narrow(x) => x,
        U128sFromFelt252Result::Wide(_) => { return false; },
    };
    let x: Acc7 = match downcast(low) {
        Some(x) => x,
        None => { return false; },
    };
    let (x, d0) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a0, d0, c0)) {
        return false;
    }
    let (x, d1) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a1, d1, c1)) {
        return false;
    }
    let (x, d2) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a2, d2, c2)) {
        return false;
    }
    let (x, d3) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a3, d3, c3)) {
        return false;
    }
    let (x, d4) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a4, d4, c4)) {
        return false;
    }
    let (x, d5) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a5, d5, c5)) {
        return false;
    }
    let (x, d6) = bounded_int_div_rem(x, q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a6, d6, c6)) {
        return false;
    }
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(hint_quotient_inv(a7, x, c7)) {
        return false;
    }
    true
}

/// Everything after the hash: s1 and t unpacked into their lazy transforms, the norm bound,
/// and each public-key slot checked against both transforms. The transforms stay on the
/// stack (no output boxes to write and read back) and reach the key check as arguments of
/// [`check_slot_zq`]. Once the s1 transform exists, a reject only clears `ok` (no early
/// exit has to drop the live transform). Same verdicts as `unpack_ntt_512_n`,
/// `unpack_ntt_512_d`, the bound and `unpack_512_zq_check` in sequence.
#[inline(never)]
pub(crate) fn verify_tail(
    s1_slots: @Box<[felt252; 29]>, t_slots: @Box<[felt252; 29]>, mut msg: Span<u16>,
    mut public_key: Span<felt252>,
) -> bool {
    // A loop that never iterates gives this function an unknown ap change: the caller then
    // keeps what it needs afterwards in locals instead of ap cells further away than an
    // offset can reach across this function's stack.
    let mut i: u32 = msg.len();
    while i == 0 {
        i += 1;
    }
    let q = packing_q_cell();
    let mut norm_n: felt252 = 0;
    let [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28] = (*s1_slots).unbox();
    let [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71] = match unpack_chunk_ntt_n4(s0, s1, s2, s3, ref norm_n, q, 1) {
        Some(v) => v,
        None => { return false; },
    };
    let [g72, g73, g74, g75, g76, g77, g78, g79, g80, g81, g82, g83, g84, g85, g86, g87, g88, g89, g90, g91, g92, g93, g94, g95, g96, g97, g98, g99, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119, g120, g121, g122, g123, g124, g125, g126, g127, g128, g129, g130, g131, g132, g133, g134, g135, g136, g137, g138, g139, g140, g141, g142, g143] = match unpack_chunk_ntt_n4(s4, s5, s6, s7, ref norm_n, q, 1) {
        Some(v) => v,
        None => { return false; },
    };
    let [g144, g145, g146, g147, g148, g149, g150, g151, g152, g153, g154, g155, g156, g157, g158, g159, g160, g161, g162, g163, g164, g165, g166, g167, g168, g169, g170, g171, g172, g173, g174, g175, g176, g177, g178, g179, g180, g181, g182, g183, g184, g185, g186, g187, g188, g189, g190, g191, g192, g193, g194, g195, g196, g197, g198, g199, g200, g201, g202, g203, g204, g205, g206, g207, g208, g209, g210, g211, g212, g213, g214, g215] = match unpack_chunk_ntt_n4(s8, s9, s10, s11, ref norm_n, q, 1) {
        Some(v) => v,
        None => { return false; },
    };
    let [g216, g217, g218, g219, g220, g221, g222, g223, g224, g225, g226, g227, g228, g229, g230, g231, g232, g233, g234, g235, g236, g237, g238, g239, g240, g241, g242, g243, g244, g245, g246, g247, g248, g249, g250, g251, g252, g253, g254, g255, g256, g257, g258, g259, g260, g261, g262, g263, g264, g265, g266, g267, g268, g269, g270, g271, g272, g273, g274, g275, g276, g277, g278, g279, g280, g281, g282, g283, g284, g285, g286, g287] = match unpack_chunk_ntt_n4(s12, s13, s14, s15, ref norm_n, q, 1) {
        Some(v) => v,
        None => { return false; },
    };
    let [g288, g289, g290, g291, g292, g293, g294, g295, g296, g297, g298, g299, g300, g301, g302, g303, g304, g305, g306, g307, g308, g309, g310, g311, g312, g313, g314, g315, g316, g317, g318, g319, g320, g321, g322, g323, g324, g325, g326, g327, g328, g329, g330, g331, g332, g333, g334, g335, g336, g337, g338, g339, g340, g341, g342, g343, g344, g345, g346, g347, g348, g349, g350, g351, g352, g353, g354, g355, g356, g357, g358, g359] = match unpack_chunk_ntt_n4(s16, s17, s18, s19, ref norm_n, q, 1479) {
        Some(v) => v,
        None => { return false; },
    };
    let [g360, g361, g362, g363, g364, g365, g366, g367, g368, g369, g370, g371, g372, g373, g374, g375, g376, g377, g378, g379, g380, g381, g382, g383, g384, g385, g386, g387, g388, g389, g390, g391, g392, g393, g394, g395, g396, g397, g398, g399, g400, g401, g402, g403, g404, g405, g406, g407, g408, g409, g410, g411, g412, g413, g414, g415, g416, g417, g418, g419, g420, g421, g422, g423, g424, g425, g426, g427, g428, g429, g430, g431] = match unpack_chunk_ntt_n4(s20, s21, s22, s23, ref norm_n, q, 1479) {
        Some(v) => v,
        None => { return false; },
    };
    let [g432, g433, g434, g435, g436, g437, g438, g439, g440, g441, g442, g443, g444, g445, g446, g447, g448, g449, g450, g451, g452, g453, g454, g455, g456, g457, g458, g459, g460, g461, g462, g463, g464, g465, g466, g467, g468, g469, g470, g471, g472, g473, g474, g475, g476, g477, g478, g479, g480, g481, g482, g483, g484, g485, g486, g487, g488, g489, g490, g491, g492, g493, g494, g495, g496, g497, g498, g499, g500, g501, g502, g503] = match unpack_chunk_ntt_n4_inl(s24, s25, s26, s27, ref norm_n, q, 1479) {
        Some(v) => v,
        None => { return false; },
    };
    // Q51: the last slot must split Narrow (high half 0); no u256 merge, no zero test.
    let low = match u128s_from_felt252(s28) {
        U128sFromFelt252Result::Narrow(x) => x,
        U128sFromFelt252Result::Wide(_) => { return false; },
    };
    let value: Acc7 = match downcast(low) {
        Some(v) => v,
        None => { return false; },
    };
    let (e0, e1, e2, e3, e4, e5, e6, e7) = digits8_np(value, ref norm_n, q);
    let mut ok = true;
    // Constants fetched again where they are used: a cell from the top of this long
    // function would sit further from its use than an ap offset can reach.
    let q = packing_q_cell();
    let mut norm_d: felt252 = 0;
    let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28] = (*t_slots).unbox();
    let ([c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, c0_29, c0_30, c0_31, c0_32, c0_33, c0_34, c0_35, c0_36, c0_37, c0_38, c0_39, c0_40, c0_41, c0_42, c0_43, c0_44, c0_45, c0_46, c0_47, c0_48, c0_49, c0_50, c0_51, c0_52, c0_53, c0_54, c0_55, c0_56, c0_57, c0_58, c0_59, c0_60, c0_61, c0_62, c0_63, c0_64, c0_65, c0_66, c0_67, c0_68, c0_69, c0_70, c0_71], chunk_ok) = unpack_chunk_ntt_d4(t0, t1, t2, t3, ref msg, ref norm_d, q, 1);
    ok = ok & chunk_ok;
    let ([c0_72, c0_73, c0_74, c0_75, c0_76, c0_77, c0_78, c0_79, c0_80, c0_81, c0_82, c0_83, c0_84, c0_85, c0_86, c0_87, c0_88, c0_89, c0_90, c0_91, c0_92, c0_93, c0_94, c0_95, c0_96, c0_97, c0_98, c0_99, c0_100, c0_101, c0_102, c0_103, c0_104, c0_105, c0_106, c0_107, c0_108, c0_109, c0_110, c0_111, c0_112, c0_113, c0_114, c0_115, c0_116, c0_117, c0_118, c0_119, c0_120, c0_121, c0_122, c0_123, c0_124, c0_125, c0_126, c0_127, c0_128, c0_129, c0_130, c0_131, c0_132, c0_133, c0_134, c0_135, c0_136, c0_137, c0_138, c0_139, c0_140, c0_141, c0_142, c0_143], chunk_ok) = unpack_chunk_ntt_d4(t4, t5, t6, t7, ref msg, ref norm_d, q, 1);
    ok = ok & chunk_ok;
    let ([c0_144, c0_145, c0_146, c0_147, c0_148, c0_149, c0_150, c0_151, c0_152, c0_153, c0_154, c0_155, c0_156, c0_157, c0_158, c0_159, c0_160, c0_161, c0_162, c0_163, c0_164, c0_165, c0_166, c0_167, c0_168, c0_169, c0_170, c0_171, c0_172, c0_173, c0_174, c0_175, c0_176, c0_177, c0_178, c0_179, c0_180, c0_181, c0_182, c0_183, c0_184, c0_185, c0_186, c0_187, c0_188, c0_189, c0_190, c0_191, c0_192, c0_193, c0_194, c0_195, c0_196, c0_197, c0_198, c0_199, c0_200, c0_201, c0_202, c0_203, c0_204, c0_205, c0_206, c0_207, c0_208, c0_209, c0_210, c0_211, c0_212, c0_213, c0_214, c0_215], chunk_ok) = unpack_chunk_ntt_d4(t8, t9, t10, t11, ref msg, ref norm_d, q, 1);
    ok = ok & chunk_ok;
    let ([c0_216, c0_217, c0_218, c0_219, c0_220, c0_221, c0_222, c0_223, c0_224, c0_225, c0_226, c0_227, c0_228, c0_229, c0_230, c0_231, c0_232, c0_233, c0_234, c0_235, c0_236, c0_237, c0_238, c0_239, c0_240, c0_241, c0_242, c0_243, c0_244, c0_245, c0_246, c0_247, c0_248, c0_249, c0_250, c0_251, c0_252, c0_253, c0_254, c0_255, c0_256, c0_257, c0_258, c0_259, c0_260, c0_261, c0_262, c0_263, c0_264, c0_265, c0_266, c0_267, c0_268, c0_269, c0_270, c0_271, c0_272, c0_273, c0_274, c0_275, c0_276, c0_277, c0_278, c0_279, c0_280, c0_281, c0_282, c0_283, c0_284, c0_285, c0_286, c0_287], chunk_ok) = unpack_chunk_ntt_d4(t12, t13, t14, t15, ref msg, ref norm_d, q, 1);
    ok = ok & chunk_ok;
    let ([c0_288, c0_289, c0_290, c0_291, c0_292, c0_293, c0_294, c0_295, c0_296, c0_297, c0_298, c0_299, c0_300, c0_301, c0_302, c0_303, c0_304, c0_305, c0_306, c0_307, c0_308, c0_309, c0_310, c0_311, c0_312, c0_313, c0_314, c0_315, c0_316, c0_317, c0_318, c0_319, c0_320, c0_321, c0_322, c0_323, c0_324, c0_325, c0_326, c0_327, c0_328, c0_329, c0_330, c0_331, c0_332, c0_333, c0_334, c0_335, c0_336, c0_337, c0_338, c0_339, c0_340, c0_341, c0_342, c0_343, c0_344, c0_345, c0_346, c0_347, c0_348, c0_349, c0_350, c0_351, c0_352, c0_353, c0_354, c0_355, c0_356, c0_357, c0_358, c0_359], chunk_ok) = unpack_chunk_ntt_d4(t16, t17, t18, t19, ref msg, ref norm_d, q, 1479);
    ok = ok & chunk_ok;
    let ([c0_360, c0_361, c0_362, c0_363, c0_364, c0_365, c0_366, c0_367, c0_368, c0_369, c0_370, c0_371, c0_372, c0_373, c0_374, c0_375, c0_376, c0_377, c0_378, c0_379, c0_380, c0_381, c0_382, c0_383, c0_384, c0_385, c0_386, c0_387, c0_388, c0_389, c0_390, c0_391, c0_392, c0_393, c0_394, c0_395, c0_396, c0_397, c0_398, c0_399, c0_400, c0_401, c0_402, c0_403, c0_404, c0_405, c0_406, c0_407, c0_408, c0_409, c0_410, c0_411, c0_412, c0_413, c0_414, c0_415, c0_416, c0_417, c0_418, c0_419, c0_420, c0_421, c0_422, c0_423, c0_424, c0_425, c0_426, c0_427, c0_428, c0_429, c0_430, c0_431], chunk_ok) = unpack_chunk_ntt_d4(t20, t21, t22, t23, ref msg, ref norm_d, q, 1479);
    ok = ok & chunk_ok;
    let ([c0_432, c0_433, c0_434, c0_435, c0_436, c0_437, c0_438, c0_439, c0_440, c0_441, c0_442, c0_443, c0_444, c0_445, c0_446, c0_447, c0_448, c0_449, c0_450, c0_451, c0_452, c0_453, c0_454, c0_455, c0_456, c0_457, c0_458, c0_459, c0_460, c0_461, c0_462, c0_463, c0_464, c0_465, c0_466, c0_467, c0_468, c0_469, c0_470, c0_471, c0_472, c0_473, c0_474, c0_475, c0_476, c0_477, c0_478, c0_479, c0_480, c0_481, c0_482, c0_483, c0_484, c0_485, c0_486, c0_487, c0_488, c0_489, c0_490, c0_491, c0_492, c0_493, c0_494, c0_495, c0_496, c0_497, c0_498, c0_499, c0_500, c0_501, c0_502, c0_503], chunk_ok) = unpack_chunk_ntt_d4(t24, t25, t26, t27, ref msg, ref norm_d, q, 1479);
    ok = ok & chunk_ok;
    // Q51: the last slot must split Narrow (high half 0); no u256 merge, no zero test.
    let low = match u128s_from_felt252(t28) {
        U128sFromFelt252Result::Narrow(x) => x,
        U128sFromFelt252Result::Wide(_) => {
            ok = false;
            0
        },
    };
    let value: Acc7 = match downcast(low) {
        Some(v) => v,
        None => {
            ok = false;
            ZERO_ACC7
        },
    };
    let [m0, m1, m2, m3, m4, m5, m6, m7] = match msg.multi_pop_front::<8>() {
        Some(b) => (*b).unbox(),
        None => {
            ok = false;
            [0, 0, 0, 0, 0, 0, 0, 0]
        },
    };
    let (te0, te1, te2, te3, te4, te5, te6, te7) = digits8_d(value, [m0, m1, m2, m3, m4, m5, m6, m7], ref norm_d, q);
    let [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77, a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, a92, a93, a94, a95, a96, a97, a98, a99, a100, a101, a102, a103, a104, a105, a106, a107, a108, a109, a110, a111, a112, a113, a114, a115, a116, a117, a118, a119, a120, a121, a122, a123, a124, a125, a126, a127, a128, a129, a130, a131, a132, a133, a134, a135, a136, a137, a138, a139, a140, a141, a142, a143, a144, a145, a146, a147, a148, a149, a150, a151, a152, a153, a154, a155, a156, a157, a158, a159, a160, a161, a162, a163, a164, a165, a166, a167, a168, a169, a170, a171, a172, a173, a174, a175, a176, a177, a178, a179, a180, a181, a182, a183, a184, a185, a186, a187, a188, a189, a190, a191, a192, a193, a194, a195, a196, a197, a198, a199, a200, a201, a202, a203, a204, a205, a206, a207, a208, a209, a210, a211, a212, a213, a214, a215, a216, a217, a218, a219, a220, a221, a222, a223, a224, a225, a226, a227, a228, a229, a230, a231, a232, a233, a234, a235, a236, a237, a238, a239, a240, a241, a242, a243, a244, a245, a246, a247, a248, a249, a250, a251, a252, a253, a254, a255, a256, a257, a258, a259, a260, a261, a262, a263, a264, a265, a266, a267, a268, a269, a270, a271, a272, a273, a274, a275, a276, a277, a278, a279, a280, a281, a282, a283, a284, a285, a286, a287, a288, a289, a290, a291, a292, a293, a294, a295, a296, a297, a298, a299, a300, a301, a302, a303, a304, a305, a306, a307, a308, a309, a310, a311, a312, a313, a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a430, a431, a432, a433, a434, a435, a436, a437, a438, a439, a440, a441, a442, a443, a444, a445, a446, a447, a448, a449, a450, a451, a452, a453, a454, a455, a456, a457, a458, a459, a460, a461, a462, a463, a464, a465, a466, a467, a468, a469, a470, a471, a472, a473, a474, a475, a476, a477, a478, a479, a480, a481, a482, a483, a484, a485, a486, a487, a488, a489, a490, a491, a492, a493, a494, a495, a496, a497, a498, a499, a500, a501, a502, a503, a504, a505, a506, a507, a508, a509, a510, a511] = pqbench_ntt::falcon512_fast::ntt_falcon512_fast_lazy_arr([g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, g81, g82, g83, g84, g85, g86, g87, g88, g89, g90, g91, g92, g93, g94, g95, g96, g97, g98, g99, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119, g120, g121, g122, g123, g124, g125, g126, g127, g128, g129, g130, g131, g132, g133, g134, g135, g136, g137, g138, g139, g140, g141, g142, g143, g144, g145, g146, g147, g148, g149, g150, g151, g152, g153, g154, g155, g156, g157, g158, g159, g160, g161, g162, g163, g164, g165, g166, g167, g168, g169, g170, g171, g172, g173, g174, g175, g176, g177, g178, g179, g180, g181, g182, g183, g184, g185, g186, g187, g188, g189, g190, g191, g192, g193, g194, g195, g196, g197, g198, g199, g200, g201, g202, g203, g204, g205, g206, g207, g208, g209, g210, g211, g212, g213, g214, g215, g216, g217, g218, g219, g220, g221, g222, g223, g224, g225, g226, g227, g228, g229, g230, g231, g232, g233, g234, g235, g236, g237, g238, g239, g240, g241, g242, g243, g244, g245, g246, g247, g248, g249, g250, g251, g252, g253, g254, g255, g256 * 1479, g257 * 1479, g258 * 1479, g259 * 1479, g260 * 1479, g261 * 1479, g262 * 1479, g263 * 1479, g264 * 1479, g265 * 1479, g266 * 1479, g267 * 1479, g268 * 1479, g269 * 1479, g270 * 1479, g271 * 1479, g272 * 1479, g273 * 1479, g274 * 1479, g275 * 1479, g276 * 1479, g277 * 1479, g278 * 1479, g279 * 1479, g280 * 1479, g281 * 1479, g282 * 1479, g283 * 1479, g284 * 1479, g285 * 1479, g286 * 1479, g287 * 1479, g288, g289, g290, g291, g292, g293, g294, g295, g296, g297, g298, g299, g300, g301, g302, g303, g304, g305, g306, g307, g308, g309, g310, g311, g312, g313, g314, g315, g316, g317, g318, g319, g320, g321, g322, g323, g324, g325, g326, g327, g328, g329, g330, g331, g332, g333, g334, g335, g336, g337, g338, g339, g340, g341, g342, g343, g344, g345, g346, g347, g348, g349, g350, g351, g352, g353, g354, g355, g356, g357, g358, g359, g360, g361, g362, g363, g364, g365, g366, g367, g368, g369, g370, g371, g372, g373, g374, g375, g376, g377, g378, g379, g380, g381, g382, g383, g384, g385, g386, g387, g388, g389, g390, g391, g392, g393, g394, g395, g396, g397, g398, g399, g400, g401, g402, g403, g404, g405, g406, g407, g408, g409, g410, g411, g412, g413, g414, g415, g416, g417, g418, g419, g420, g421, g422, g423, g424, g425, g426, g427, g428, g429, g430, g431, g432, g433, g434, g435, g436, g437, g438, g439, g440, g441, g442, g443, g444, g445, g446, g447, g448, g449, g450, g451, g452, g453, g454, g455, g456, g457, g458, g459, g460, g461, g462, g463, g464, g465, g466, g467, g468, g469, g470, g471, g472, g473, g474, g475, g476, g477, g478, g479, g480, g481, g482, g483, g484, g485, g486, g487, g488, g489, g490, g491, g492, g493, g494, g495, g496, g497, g498, g499, g500, g501, g502, g503, e0 * 1479, e1 * 1479, e2 * 1479, e3 * 1479, e4 * 1479, e5 * 1479, e6 * 1479, e7 * 1479], 0);
    let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127, c128, c129, c130, c131, c132, c133, c134, c135, c136, c137, c138, c139, c140, c141, c142, c143, c144, c145, c146, c147, c148, c149, c150, c151, c152, c153, c154, c155, c156, c157, c158, c159, c160, c161, c162, c163, c164, c165, c166, c167, c168, c169, c170, c171, c172, c173, c174, c175, c176, c177, c178, c179, c180, c181, c182, c183, c184, c185, c186, c187, c188, c189, c190, c191, c192, c193, c194, c195, c196, c197, c198, c199, c200, c201, c202, c203, c204, c205, c206, c207, c208, c209, c210, c211, c212, c213, c214, c215, c216, c217, c218, c219, c220, c221, c222, c223, c224, c225, c226, c227, c228, c229, c230, c231, c232, c233, c234, c235, c236, c237, c238, c239, c240, c241, c242, c243, c244, c245, c246, c247, c248, c249, c250, c251, c252, c253, c254, c255, c256, c257, c258, c259, c260, c261, c262, c263, c264, c265, c266, c267, c268, c269, c270, c271, c272, c273, c274, c275, c276, c277, c278, c279, c280, c281, c282, c283, c284, c285, c286, c287, c288, c289, c290, c291, c292, c293, c294, c295, c296, c297, c298, c299, c300, c301, c302, c303, c304, c305, c306, c307, c308, c309, c310, c311, c312, c313, c314, c315, c316, c317, c318, c319, c320, c321, c322, c323, c324, c325, c326, c327, c328, c329, c330, c331, c332, c333, c334, c335, c336, c337, c338, c339, c340, c341, c342, c343, c344, c345, c346, c347, c348, c349, c350, c351, c352, c353, c354, c355, c356, c357, c358, c359, c360, c361, c362, c363, c364, c365, c366, c367, c368, c369, c370, c371, c372, c373, c374, c375, c376, c377, c378, c379, c380, c381, c382, c383, c384, c385, c386, c387, c388, c389, c390, c391, c392, c393, c394, c395, c396, c397, c398, c399, c400, c401, c402, c403, c404, c405, c406, c407, c408, c409, c410, c411, c412, c413, c414, c415, c416, c417, c418, c419, c420, c421, c422, c423, c424, c425, c426, c427, c428, c429, c430, c431, c432, c433, c434, c435, c436, c437, c438, c439, c440, c441, c442, c443, c444, c445, c446, c447, c448, c449, c450, c451, c452, c453, c454, c455, c456, c457, c458, c459, c460, c461, c462, c463, c464, c465, c466, c467, c468, c469, c470, c471, c472, c473, c474, c475, c476, c477, c478, c479, c480, c481, c482, c483, c484, c485, c486, c487, c488, c489, c490, c491, c492, c493, c494, c495, c496, c497, c498, c499, c500, c501, c502, c503, c504, c505, c506, c507, c508, c509, c510, c511] = pqbench_ntt::falcon512_fast::ntt_falcon512_fast_lazy_arr([c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, c0_29, c0_30, c0_31, c0_32, c0_33, c0_34, c0_35, c0_36, c0_37, c0_38, c0_39, c0_40, c0_41, c0_42, c0_43, c0_44, c0_45, c0_46, c0_47, c0_48, c0_49, c0_50, c0_51, c0_52, c0_53, c0_54, c0_55, c0_56, c0_57, c0_58, c0_59, c0_60, c0_61, c0_62, c0_63, c0_64, c0_65, c0_66, c0_67, c0_68, c0_69, c0_70, c0_71, c0_72, c0_73, c0_74, c0_75, c0_76, c0_77, c0_78, c0_79, c0_80, c0_81, c0_82, c0_83, c0_84, c0_85, c0_86, c0_87, c0_88, c0_89, c0_90, c0_91, c0_92, c0_93, c0_94, c0_95, c0_96, c0_97, c0_98, c0_99, c0_100, c0_101, c0_102, c0_103, c0_104, c0_105, c0_106, c0_107, c0_108, c0_109, c0_110, c0_111, c0_112, c0_113, c0_114, c0_115, c0_116, c0_117, c0_118, c0_119, c0_120, c0_121, c0_122, c0_123, c0_124, c0_125, c0_126, c0_127, c0_128, c0_129, c0_130, c0_131, c0_132, c0_133, c0_134, c0_135, c0_136, c0_137, c0_138, c0_139, c0_140, c0_141, c0_142, c0_143, c0_144, c0_145, c0_146, c0_147, c0_148, c0_149, c0_150, c0_151, c0_152, c0_153, c0_154, c0_155, c0_156, c0_157, c0_158, c0_159, c0_160, c0_161, c0_162, c0_163, c0_164, c0_165, c0_166, c0_167, c0_168, c0_169, c0_170, c0_171, c0_172, c0_173, c0_174, c0_175, c0_176, c0_177, c0_178, c0_179, c0_180, c0_181, c0_182, c0_183, c0_184, c0_185, c0_186, c0_187, c0_188, c0_189, c0_190, c0_191, c0_192, c0_193, c0_194, c0_195, c0_196, c0_197, c0_198, c0_199, c0_200, c0_201, c0_202, c0_203, c0_204, c0_205, c0_206, c0_207, c0_208, c0_209, c0_210, c0_211, c0_212, c0_213, c0_214, c0_215, c0_216, c0_217, c0_218, c0_219, c0_220, c0_221, c0_222, c0_223, c0_224, c0_225, c0_226, c0_227, c0_228, c0_229, c0_230, c0_231, c0_232, c0_233, c0_234, c0_235, c0_236, c0_237, c0_238, c0_239, c0_240, c0_241, c0_242, c0_243, c0_244, c0_245, c0_246, c0_247, c0_248, c0_249, c0_250, c0_251, c0_252, c0_253, c0_254, c0_255, c0_256 * 1479, c0_257 * 1479, c0_258 * 1479, c0_259 * 1479, c0_260 * 1479, c0_261 * 1479, c0_262 * 1479, c0_263 * 1479, c0_264 * 1479, c0_265 * 1479, c0_266 * 1479, c0_267 * 1479, c0_268 * 1479, c0_269 * 1479, c0_270 * 1479, c0_271 * 1479, c0_272 * 1479, c0_273 * 1479, c0_274 * 1479, c0_275 * 1479, c0_276 * 1479, c0_277 * 1479, c0_278 * 1479, c0_279 * 1479, c0_280 * 1479, c0_281 * 1479, c0_282 * 1479, c0_283 * 1479, c0_284 * 1479, c0_285 * 1479, c0_286 * 1479, c0_287 * 1479, c0_288, c0_289, c0_290, c0_291, c0_292, c0_293, c0_294, c0_295, c0_296, c0_297, c0_298, c0_299, c0_300, c0_301, c0_302, c0_303, c0_304, c0_305, c0_306, c0_307, c0_308, c0_309, c0_310, c0_311, c0_312, c0_313, c0_314, c0_315, c0_316, c0_317, c0_318, c0_319, c0_320, c0_321, c0_322, c0_323, c0_324, c0_325, c0_326, c0_327, c0_328, c0_329, c0_330, c0_331, c0_332, c0_333, c0_334, c0_335, c0_336, c0_337, c0_338, c0_339, c0_340, c0_341, c0_342, c0_343, c0_344, c0_345, c0_346, c0_347, c0_348, c0_349, c0_350, c0_351, c0_352, c0_353, c0_354, c0_355, c0_356, c0_357, c0_358, c0_359, c0_360, c0_361, c0_362, c0_363, c0_364, c0_365, c0_366, c0_367, c0_368, c0_369, c0_370, c0_371, c0_372, c0_373, c0_374, c0_375, c0_376, c0_377, c0_378, c0_379, c0_380, c0_381, c0_382, c0_383, c0_384, c0_385, c0_386, c0_387, c0_388, c0_389, c0_390, c0_391, c0_392, c0_393, c0_394, c0_395, c0_396, c0_397, c0_398, c0_399, c0_400, c0_401, c0_402, c0_403, c0_404, c0_405, c0_406, c0_407, c0_408, c0_409, c0_410, c0_411, c0_412, c0_413, c0_414, c0_415, c0_416, c0_417, c0_418, c0_419, c0_420, c0_421, c0_422, c0_423, c0_424, c0_425, c0_426, c0_427, c0_428, c0_429, c0_430, c0_431, c0_432, c0_433, c0_434, c0_435, c0_436, c0_437, c0_438, c0_439, c0_440, c0_441, c0_442, c0_443, c0_444, c0_445, c0_446, c0_447, c0_448, c0_449, c0_450, c0_451, c0_452, c0_453, c0_454, c0_455, c0_456, c0_457, c0_458, c0_459, c0_460, c0_461, c0_462, c0_463, c0_464, c0_465, c0_466, c0_467, c0_468, c0_469, c0_470, c0_471, c0_472, c0_473, c0_474, c0_475, c0_476, c0_477, c0_478, c0_479, c0_480, c0_481, c0_482, c0_483, c0_484, c0_485, c0_486, c0_487, c0_488, c0_489, c0_490, c0_491, c0_492, c0_493, c0_494, c0_495, c0_496, c0_497, c0_498, c0_499, c0_500, c0_501, c0_502, c0_503, te0 * 1479, te1 * 1479, te2 * 1479, te3 * 1479, te4 * 1479, te5 * 1479, te6 * 1479, te7 * 1479], crate::falcon::HINT_NTT_OFFSET);
    let bound: Option<corelib_imports::bounded_int::BoundedInt<0, 34034726>> = downcast(norm_n + norm_d);
    if bound.is_none() {
        ok = false;
    }
    let q = packing_q_cell();
    let [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28] = match public_key.multi_pop_front::<29>() {
        Some(b) => (*b).unbox(),
        None => { return false; },
    };
    ok = ok & check_slot_zq(p0, [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17], [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17], q);
    ok = ok & check_slot_zq(p1, [a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35], [c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35], q);
    ok = ok & check_slot_zq(p2, [a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53], [c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53], q);
    ok = ok & check_slot_zq(p3, [a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71], [c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71], q);
    ok = ok & check_slot_zq(p4, [a72, a73, a74, a75, a76, a77, a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89], [c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89], q);
    ok = ok & check_slot_zq(p5, [a90, a91, a92, a93, a94, a95, a96, a97, a98, a99, a100, a101, a102, a103, a104, a105, a106, a107], [c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107], q);
    ok = ok & check_slot_zq(p6, [a108, a109, a110, a111, a112, a113, a114, a115, a116, a117, a118, a119, a120, a121, a122, a123, a124, a125], [c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125], q);
    ok = ok & check_slot_zq(p7, [a126, a127, a128, a129, a130, a131, a132, a133, a134, a135, a136, a137, a138, a139, a140, a141, a142, a143], [c126, c127, c128, c129, c130, c131, c132, c133, c134, c135, c136, c137, c138, c139, c140, c141, c142, c143], q);
    ok = ok & check_slot_zq(p8, [a144, a145, a146, a147, a148, a149, a150, a151, a152, a153, a154, a155, a156, a157, a158, a159, a160, a161], [c144, c145, c146, c147, c148, c149, c150, c151, c152, c153, c154, c155, c156, c157, c158, c159, c160, c161], q);
    ok = ok & check_slot_zq(p9, [a162, a163, a164, a165, a166, a167, a168, a169, a170, a171, a172, a173, a174, a175, a176, a177, a178, a179], [c162, c163, c164, c165, c166, c167, c168, c169, c170, c171, c172, c173, c174, c175, c176, c177, c178, c179], q);
    ok = ok & check_slot_zq(p10, [a180, a181, a182, a183, a184, a185, a186, a187, a188, a189, a190, a191, a192, a193, a194, a195, a196, a197], [c180, c181, c182, c183, c184, c185, c186, c187, c188, c189, c190, c191, c192, c193, c194, c195, c196, c197], q);
    ok = ok & check_slot_zq(p11, [a198, a199, a200, a201, a202, a203, a204, a205, a206, a207, a208, a209, a210, a211, a212, a213, a214, a215], [c198, c199, c200, c201, c202, c203, c204, c205, c206, c207, c208, c209, c210, c211, c212, c213, c214, c215], q);
    ok = ok & check_slot_zq(p12, [a216, a217, a218, a219, a220, a221, a222, a223, a224, a225, a226, a227, a228, a229, a230, a231, a232, a233], [c216, c217, c218, c219, c220, c221, c222, c223, c224, c225, c226, c227, c228, c229, c230, c231, c232, c233], q);
    ok = ok & check_slot_zq(p13, [a234, a235, a236, a237, a238, a239, a240, a241, a242, a243, a244, a245, a246, a247, a248, a249, a250, a251], [c234, c235, c236, c237, c238, c239, c240, c241, c242, c243, c244, c245, c246, c247, c248, c249, c250, c251], q);
    ok = ok & check_slot_zq(p14, [a252, a253, a254, a255, a256, a257, a258, a259, a260, a261, a262, a263, a264, a265, a266, a267, a268, a269], [c252, c253, c254, c255, c256, c257, c258, c259, c260, c261, c262, c263, c264, c265, c266, c267, c268, c269], q);
    ok = ok & check_slot_zq(p15, [a270, a271, a272, a273, a274, a275, a276, a277, a278, a279, a280, a281, a282, a283, a284, a285, a286, a287], [c270, c271, c272, c273, c274, c275, c276, c277, c278, c279, c280, c281, c282, c283, c284, c285, c286, c287], q);
    ok = ok & check_slot_zq(p16, [a288, a289, a290, a291, a292, a293, a294, a295, a296, a297, a298, a299, a300, a301, a302, a303, a304, a305], [c288, c289, c290, c291, c292, c293, c294, c295, c296, c297, c298, c299, c300, c301, c302, c303, c304, c305], q);
    ok = ok & check_slot_zq(p17, [a306, a307, a308, a309, a310, a311, a312, a313, a314, a315, a316, a317, a318, a319, a320, a321, a322, a323], [c306, c307, c308, c309, c310, c311, c312, c313, c314, c315, c316, c317, c318, c319, c320, c321, c322, c323], q);
    ok = ok & check_slot_zq(p18, [a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341], [c324, c325, c326, c327, c328, c329, c330, c331, c332, c333, c334, c335, c336, c337, c338, c339, c340, c341], q);
    ok = ok & check_slot_zq(p19, [a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, a358, a359], [c342, c343, c344, c345, c346, c347, c348, c349, c350, c351, c352, c353, c354, c355, c356, c357, c358, c359], q);
    ok = ok & check_slot_zq(p20, [a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377], [c360, c361, c362, c363, c364, c365, c366, c367, c368, c369, c370, c371, c372, c373, c374, c375, c376, c377], q);
    ok = ok & check_slot_zq(p21, [a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395], [c378, c379, c380, c381, c382, c383, c384, c385, c386, c387, c388, c389, c390, c391, c392, c393, c394, c395], q);
    ok = ok & check_slot_zq(p22, [a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413], [c396, c397, c398, c399, c400, c401, c402, c403, c404, c405, c406, c407, c408, c409, c410, c411, c412, c413], q);
    ok = ok & check_slot_zq(p23, [a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a430, a431], [c414, c415, c416, c417, c418, c419, c420, c421, c422, c423, c424, c425, c426, c427, c428, c429, c430, c431], q);
    ok = ok & check_slot_zq(p24, [a432, a433, a434, a435, a436, a437, a438, a439, a440, a441, a442, a443, a444, a445, a446, a447, a448, a449], [c432, c433, c434, c435, c436, c437, c438, c439, c440, c441, c442, c443, c444, c445, c446, c447, c448, c449], q);
    ok = ok & check_slot_zq(p25, [a450, a451, a452, a453, a454, a455, a456, a457, a458, a459, a460, a461, a462, a463, a464, a465, a466, a467], [c450, c451, c452, c453, c454, c455, c456, c457, c458, c459, c460, c461, c462, c463, c464, c465, c466, c467], q);
    ok = ok & check_slot_zq(p26, [a468, a469, a470, a471, a472, a473, a474, a475, a476, a477, a478, a479, a480, a481, a482, a483, a484, a485], [c468, c469, c470, c471, c472, c473, c474, c475, c476, c477, c478, c479, c480, c481, c482, c483, c484, c485], q);
    ok = ok & check_slot_zq(p27, [a486, a487, a488, a489, a490, a491, a492, a493, a494, a495, a496, a497, a498, a499, a500, a501, a502, a503], [c486, c487, c488, c489, c490, c491, c492, c493, c494, c495, c496, c497, c498, c499, c500, c501, c502, c503], q);
    ok & check_last_slot_zq(p28, [a504, a505, a506, a507, a508, a509, a510, a511], [c504, c505, c506, c507, c508, c509, c510, c511], q)
}
