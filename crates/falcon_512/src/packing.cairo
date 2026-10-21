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
    AddHelper,BoundedInt,DivRemHelper,MulHelper,UnitInt,bounded_int,bounded_int_div_rem,downcast,
    upcast,
};
#[feature("bounded-int-utils")]
use core::internal::bounded_int::{ConstrainHelper,SubHelper,constrain};
use corelib_imports::integer::{U128sFromFelt252Result,u128s_from_felt252};
use pqbench_ntt::L;
use crate::zq::Q;

/// Coefficients per full felt252 slot (two u128 halves of 9).
pub const VALS_PER_FELT: u32 = 18;
/// felt252 slots for 512 coefficients: 28 full slots + 1 slot with 8.
pub const PACKED_SLOTS: u32 = 29;
/// Coefficients in the last slot: 512 - 28*18.
const LAST_SLOT_VALS: u32 = 8;

const TWO_POW_128: felt252 = 0x100000000000000000000000000000000;

pub(crate) type PackingZq = BoundedInt<0,12288>;
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
        if !unpack_full_slot_u16(f0,ref coeffs,q)
            || !unpack_full_slot_u16(f1,ref coeffs,q)
            || !unpack_full_slot_u16(f2,ref coeffs,q)
            || !unpack_full_slot_u16(f3,ref coeffs,q)
            || !unpack_full_slot_u16(f4,ref coeffs,q)
            || !unpack_full_slot_u16(f5,ref coeffs,q)
            || !unpack_full_slot_u16(f6,ref coeffs,q) {
            return None;
        }
    }
    let last: u256 = (*packed.at(PACKED_SLOTS - 1)).into();
    if last.high != 0 || !unpack_half8_u16(last.low,ref coeffs,q) {
        return None;
    }
    Some(coeffs)
}

#[inline(always)]
fn unpack_full_slot_u16(felt: felt252,ref coeffs: Array<u16>,q: NonZero<PackingQ>) -> bool {
    let value: u256 = felt.into();
    unpack_half9_u16(value.low,ref coeffs,q) && unpack_half9_u16(value.high,ref coeffs,q)
}

/// Extract nine base-Q digits from a u128 half. Values below Q^9 are canonical;
/// after eight divisions the remaining quotient is the ninth digit.
#[inline(always)]
fn unpack_half9_u16(value: u128,ref coeffs: Array<u16>,q: NonZero<PackingQ>) -> bool {
    let value: Acc8 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
    let (rest,d0) = bounded_int_div_rem(value,q);
    let (rest,d1) = bounded_int_div_rem(rest,q);
    let (rest,d2) = bounded_int_div_rem(rest,q);
    let (rest,d3) = bounded_int_div_rem(rest,q);
    let (rest,d4) = bounded_int_div_rem(rest,q);
    let (rest,d5) = bounded_int_div_rem(rest,q);
    let (rest,d6) = bounded_int_div_rem(rest,q);
    let (rest,d7) = bounded_int_div_rem(rest,q);
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
fn unpack_half8_u16(value: u128,ref coeffs: Array<u16>,q: NonZero<PackingQ>) -> bool {
    let value: Acc7 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
    let (rest,d0) = bounded_int_div_rem(value,q);
    let (rest,d1) = bounded_int_div_rem(rest,q);
    let (rest,d2) = bounded_int_div_rem(rest,q);
    let (rest,d3) = bounded_int_div_rem(rest,q);
    let (rest,d4) = bounded_int_div_rem(rest,q);
    let (rest,d5) = bounded_int_div_rem(rest,q);
    let (rest,d6) = bounded_int_div_rem(rest,q);
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
fn unpack_full_slot_zq(felt: felt252,ref coeffs: Array<PackingZq>,q: NonZero<PackingQ>) -> bool {
    let value: u256 = felt.into();
    unpack_half9_zq(value.low,ref coeffs,q) && unpack_half9_zq(value.high,ref coeffs,q)
}

/// Extract nine base-Q digits from a u128 half. Values below Q^9 are canonical;
/// after eight divisions the remaining quotient is the ninth digit.
#[inline(always)]
fn unpack_half9_zq(value: u128,ref coeffs: Array<PackingZq>,q: NonZero<PackingQ>) -> bool {
    let value: Acc8 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
    let (rest,d0) = bounded_int_div_rem(value,q);
    let (rest,d1) = bounded_int_div_rem(rest,q);
    let (rest,d2) = bounded_int_div_rem(rest,q);
    let (rest,d3) = bounded_int_div_rem(rest,q);
    let (rest,d4) = bounded_int_div_rem(rest,q);
    let (rest,d5) = bounded_int_div_rem(rest,q);
    let (rest,d6) = bounded_int_div_rem(rest,q);
    let (rest,d7) = bounded_int_div_rem(rest,q);
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
fn unpack_half8_zq(value: u128,ref coeffs: Array<PackingZq>,q: NonZero<PackingQ>) -> bool {
    let value: Acc7 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
    let (rest,d0) = bounded_int_div_rem(value,q);
    let (rest,d1) = bounded_int_div_rem(rest,q);
    let (rest,d2) = bounded_int_div_rem(rest,q);
    let (rest,d3) = bounded_int_div_rem(rest,q);
    let (rest,d4) = bounded_int_div_rem(rest,q);
    let (rest,d5) = bounded_int_div_rem(rest,q);
    let (rest,d6) = bounded_int_div_rem(rest,q);
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

type CenterShiftZq = BoundedInt<6144,18432>;
type CenteredZq = BoundedInt<-6144,6144>;
impl AddZqHalf of AddHelper<PackingZq,UnitInt<6144>> {
    type Result = CenterShiftZq;
}
impl DivRemCenterShiftZq of DivRemHelper<CenterShiftZq,PackingQ> {
    type DivT = BoundedInt<0,1>;
    type RemT = PackingZq;
}
impl SubZqHalf of SubHelper<PackingZq,UnitInt<6144>> {
    type Result = CenteredZq;
}
impl MulCenteredZq of MulHelper<CenteredZq,CenteredZq> {
    type Result = BoundedInt<-37748736,37748736>;
}

/// The centered square of a digit: `(d + 6144) mod q - 6144` lies in [-6144, 6144] and is
/// congruent to `d`.
impl ConstrainZqHalf of ConstrainHelper<PackingZq,6145> {
    type LowT = BoundedInt<0,6144>;
    type HighT = BoundedInt<6145,12288>;
}

#[inline(always)]
fn center_sq_zq(d: PackingZq,q: NonZero<PackingQ>) -> felt252 {
    // One range check: d <= 6144 is its own centered value, otherwise d - q is.
    let x: felt252 = match constrain::<PackingZq,6145>(d) {
        Ok(low) => low.into(),
        Err(high) => high.into() - 12289,
    };
    x * x
}

type DiffShiftZq = BoundedInt<6145,83968>;
impl AddU16DiffOffset of AddHelper<u16,UnitInt<18433>> {
    type Result = BoundedInt<18433,83968>;
}
impl SubDiffZq of SubHelper<BoundedInt<18433,83968>,PackingZq> {
    type Result = DiffShiftZq;
}
impl DivRemDiffShiftZq of DivRemHelper<DiffShiftZq,PackingQ> {
    type DivT = BoundedInt<0,6>;
    type RemT = PackingZq;
}

/// The centered square of `m - t` mod q: `(m + 6144 + q - t) mod q - 6144` lies in
/// [-6144, 6144] and is congruent to `m - t`.
#[inline(always)]
fn center_diff_sq_zq(m: u16,t: PackingZq,q: NonZero<PackingQ>) -> felt252 {
    let offset: UnitInt<18433> = 18433;
    let half: UnitInt<6144> = 6144;
    let (_,r) = bounded_int_div_rem(bounded_int::sub(bounded_int::add(m,offset),t),q);
    let c = bounded_int::sub(r,half);
    bounded_int::mul(c,c).into()
}

/// Q57: two digits centred by one constrain tree (4 leaves) and merged once, so the
/// range-check pointer store and the branch jump are paid per pair, not per digit. Same
/// centered values as two `center_sq_zq` calls.
#[inline(always)]
fn center_pair_zq(a: PackingZq,b: PackingZq) -> (felt252,felt252) {
    match constrain::<PackingZq,6145>(a) {
        Ok(la) => match constrain::<PackingZq,6145>(b) {
            Ok(lb) => (la.into(),lb.into()),
            Err(hb) => (la.into(),hb.into() - 12289),
        },
        Err(ha) => match constrain::<PackingZq,6145>(b) {
            Ok(lb) => (ha.into() - 12289,lb.into()),
            Err(hb) => (ha.into() - 12289,hb.into() - 12289),
        },
    }
}

/// [`center_sq_zq`] for four digits with one merge point (each of the sixteen outcomes ends the group, so the range-check pointer, the gas counter and the centered values are merged once per four digits).
#[inline(always)]
fn center_sq_quad_zq(d0: PackingZq,d1: PackingZq,d2: PackingZq,d3: PackingZq) -> felt252 {
    let (x0,x1,x2,x3): (felt252,felt252,felt252,felt252) = 
    match constrain::<PackingZq,6145>(d0) {
        Ok(l0) => {
            match constrain::<PackingZq,6145>(d1) {
                Ok(l1) => {
                    match constrain::<PackingZq,6145>(d2) {
                        Ok(l2) => {
                            match constrain::<PackingZq,6145>(d3) {
                                Ok(l3) => {
                                    (l0.into(),l1.into(),l2.into(),l3.into())
                                },
                                Err(h3) => {
                                    (l0.into(),l1.into(),l2.into(),h3.into() - 12289)
                                },
                            }
                        },
                        Err(h2) => {
                            match constrain::<PackingZq,6145>(d3) {
                                Ok(l3) => {
                                    (l0.into(),l1.into(),h2.into() - 12289,l3.into())
                                },
                                Err(h3) => {
                                    (l0.into(),l1.into(),h2.into() - 12289,h3.into() - 12289)
                                },
                            }
                        },
                    }
                },
                Err(h1) => {
                    match constrain::<PackingZq,6145>(d2) {
                        Ok(l2) => {
                            match constrain::<PackingZq,6145>(d3) {
                                Ok(l3) => {
                                    (l0.into(),h1.into() - 12289,l2.into(),l3.into())
                                },
                                Err(h3) => {
                                    (l0.into(),h1.into() - 12289,l2.into(),h3.into() - 12289)
                                },
                            }
                        },
                        Err(h2) => {
                            match constrain::<PackingZq,6145>(d3) {
                                Ok(l3) => {
                                    (l0.into(),h1.into() - 12289,h2.into() - 12289,l3.into())
                                },
                                Err(h3) => {
                                    (l0.into(),h1.into() - 12289,h2.into() - 12289,h3.into() - 12289)
                                },
                            }
                        },
                    }
                },
            }
        },
        Err(h0) => {
            match constrain::<PackingZq,6145>(d1) {
                Ok(l1) => {
                    match constrain::<PackingZq,6145>(d2) {
                        Ok(l2) => {
                            match constrain::<PackingZq,6145>(d3) {
                                Ok(l3) => {
                                    (h0.into() - 12289,l1.into(),l2.into(),l3.into())
                                },
                                Err(h3) => {
                                    (h0.into() - 12289,l1.into(),l2.into(),h3.into() - 12289)
                                },
                            }
                        },
                        Err(h2) => {
                            match constrain::<PackingZq,6145>(d3) {
                                Ok(l3) => {
                                    (h0.into() - 12289,l1.into(),h2.into() - 12289,l3.into())
                                },
                                Err(h3) => {
                                    (h0.into() - 12289,l1.into(),h2.into() - 12289,h3.into() - 12289)
                                },
                            }
                        },
                    }
                },
                Err(h1) => {
                    match constrain::<PackingZq,6145>(d2) {
                        Ok(l2) => {
                            match constrain::<PackingZq,6145>(d3) {
                                Ok(l3) => {
                                    (h0.into() - 12289,h1.into() - 12289,l2.into(),l3.into())
                                },
                                Err(h3) => {
                                    (h0.into() - 12289,h1.into() - 12289,l2.into(),h3.into() - 12289)
                                },
                            }
                        },
                        Err(h2) => {
                            match constrain::<PackingZq,6145>(d3) {
                                Ok(l3) => {
                                    (h0.into() - 12289,h1.into() - 12289,h2.into() - 12289,l3.into())
                                },
                                Err(h3) => {
                                    (h0.into() - 12289,h1.into() - 12289,h2.into() - 12289,h3.into() - 12289)
                                },
                            }
                        },
                    }
                },
            }
        },
    };
    x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3
}

// Q21 BEGIN (generated by data/artifacts/q21/gen_q21.py)


#[inline(always)]
fn digits9_np8(value: Acc8,ref norm: felt252,q: NonZero<PackingQ>) -> (felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252,PackingZq) {
    let (rest,d0) = bounded_int_div_rem(value,q);
    let (rest,d1) = bounded_int_div_rem(rest,q);
    let (rest,d2) = bounded_int_div_rem(rest,q);
    let (rest,d3) = bounded_int_div_rem(rest,q);
    let (rest,d4) = bounded_int_div_rem(rest,q);
    let (rest,d5) = bounded_int_div_rem(rest,q);
    let (rest,d6) = bounded_int_div_rem(rest,q);
    let (rest,d7) = bounded_int_div_rem(rest,q);
    norm += center_sq_quad_zq(d0,d1,d2,d3);
    norm += center_sq_quad_zq(d4,d5,d6,d7);
    (d0.into(),d1.into(),d2.into(),d3.into(),d4.into(),d5.into(),d6.into(),d7.into(),rest)
}

#[inline(always)]
fn digits9_d(value: Acc8,m: [u16; 9],ref norm: felt252,q: NonZero<PackingQ>) -> (felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252) {
    let (rest,d0) = bounded_int_div_rem(value,q);
    let (rest,d1) = bounded_int_div_rem(rest,q);
    let (rest,d2) = bounded_int_div_rem(rest,q);
    let (rest,d3) = bounded_int_div_rem(rest,q);
    let (rest,d4) = bounded_int_div_rem(rest,q);
    let (rest,d5) = bounded_int_div_rem(rest,q);
    let (rest,d6) = bounded_int_div_rem(rest,q);
    let (rest,d7) = bounded_int_div_rem(rest,q);
    let [m0,m1,m2,m3,m4,m5,m6,m7,m8] = m;
    norm += center_diff_sq_zq(m0,d0,q);
    norm += center_diff_sq_zq(m1,d1,q);
    norm += center_diff_sq_zq(m2,d2,q);
    norm += center_diff_sq_zq(m3,d3,q);
    norm += center_diff_sq_zq(m4,d4,q);
    norm += center_diff_sq_zq(m5,d5,q);
    norm += center_diff_sq_zq(m6,d6,q);
    norm += center_diff_sq_zq(m7,d7,q);
    norm += center_diff_sq_zq(m8,rest,q);
    (d0.into(),d1.into(),d2.into(),d3.into(),d4.into(),d5.into(),d6.into(),d7.into(),rest.into())
}


#[inline(always)]
fn digits8_np(value: Acc7,ref norm: felt252,q: NonZero<PackingQ>) -> (felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252) {
    let (rest,d0) = bounded_int_div_rem(value,q);
    let (rest,d1) = bounded_int_div_rem(rest,q);
    let (rest,d2) = bounded_int_div_rem(rest,q);
    let (rest,d3) = bounded_int_div_rem(rest,q);
    let (rest,d4) = bounded_int_div_rem(rest,q);
    let (rest,d5) = bounded_int_div_rem(rest,q);
    let (rest,d6) = bounded_int_div_rem(rest,q);
    norm += center_sq_quad_zq(d0,d1,d2,d3);
    norm += center_sq_quad_zq(d4,d5,d6,rest);
    (d0.into(),d1.into(),d2.into(),d3.into(),d4.into(),d5.into(),d6.into(),rest.into())
}

#[inline(always)]
fn digits8_d(value: Acc7,m: [u16; 8],ref norm: felt252,q: NonZero<PackingQ>) -> (felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252) {
    let (rest,d0) = bounded_int_div_rem(value,q);
    let (rest,d1) = bounded_int_div_rem(rest,q);
    let (rest,d2) = bounded_int_div_rem(rest,q);
    let (rest,d3) = bounded_int_div_rem(rest,q);
    let (rest,d4) = bounded_int_div_rem(rest,q);
    let (rest,d5) = bounded_int_div_rem(rest,q);
    let (rest,d6) = bounded_int_div_rem(rest,q);
    let [m0,m1,m2,m3,m4,m5,m6,m7] = m;
    norm += center_diff_sq_zq(m0,d0,q);
    norm += center_diff_sq_zq(m1,d1,q);
    norm += center_diff_sq_zq(m2,d2,q);
    norm += center_diff_sq_zq(m3,d3,q);
    norm += center_diff_sq_zq(m4,d4,q);
    norm += center_diff_sq_zq(m5,d5,q);
    norm += center_diff_sq_zq(m6,d6,q);
    norm += center_diff_sq_zq(m7,rest,q);
    (d0.into(),d1.into(),d2.into(),d3.into(),d4.into(),d5.into(),d6.into(),rest.into())
}

// Q21 END

/// Seven full slots of s1 (126 digits) for the transform, their centered squares added to
/// `norm`; digits come back times `s` (see [`verify_tail`]). `None` on a non-canonical slot.
#[inline(never)]
fn unpack_chunk_ntt_n7(
    f: [felt252; 7],ref norm: felt252,q: NonZero<PackingQ>,s: felt252,
) -> Option<[felt252; 126]> {
    let [f0,f1,f2,f3,f4,f5,f6] = f;
    let (high,low) = match u128s_from_felt252(f0) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x0,x1,x2,x3,x4,x5,x6,x7,r_x8) = digits9_np8(half,ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x9,x10,x11,x12,x13,x14,x15,x16,r_x17) = digits9_np8(half,ref norm,q);
    let (a,b) = center_pair_zq(r_x8,r_x17);
    norm += a * a;
    norm += b * b;
    let x8: felt252 = r_x8.into();
    let x17: felt252 = r_x17.into();
    let (high,low) = match u128s_from_felt252(f1) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x18,x19,x20,x21,x22,x23,x24,x25,r_x26) = digits9_np8(half,ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x27,x28,x29,x30,x31,x32,x33,x34,r_x35) = digits9_np8(half,ref norm,q);
    let (a,b) = center_pair_zq(r_x26,r_x35);
    norm += a * a;
    norm += b * b;
    let x26: felt252 = r_x26.into();
    let x35: felt252 = r_x35.into();
    let (high,low) = match u128s_from_felt252(f2) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x36,x37,x38,x39,x40,x41,x42,x43,r_x44) = digits9_np8(half,ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x45,x46,x47,x48,x49,x50,x51,x52,r_x53) = digits9_np8(half,ref norm,q);
    let (a,b) = center_pair_zq(r_x44,r_x53);
    norm += a * a;
    norm += b * b;
    let x44: felt252 = r_x44.into();
    let x53: felt252 = r_x53.into();
    let (high,low) = match u128s_from_felt252(f3) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x54,x55,x56,x57,x58,x59,x60,x61,r_x62) = digits9_np8(half,ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x63,x64,x65,x66,x67,x68,x69,x70,r_x71) = digits9_np8(half,ref norm,q);
    let (a,b) = center_pair_zq(r_x62,r_x71);
    norm += a * a;
    norm += b * b;
    let x62: felt252 = r_x62.into();
    let x71: felt252 = r_x71.into();
    let (high,low) = match u128s_from_felt252(f4) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x72,x73,x74,x75,x76,x77,x78,x79,r_x80) = digits9_np8(half,ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x81,x82,x83,x84,x85,x86,x87,x88,r_x89) = digits9_np8(half,ref norm,q);
    let (a,b) = center_pair_zq(r_x80,r_x89);
    norm += a * a;
    norm += b * b;
    let x80: felt252 = r_x80.into();
    let x89: felt252 = r_x89.into();
    let (high,low) = match u128s_from_felt252(f5) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x90,x91,x92,x93,x94,x95,x96,x97,r_x98) = digits9_np8(half,ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x99,x100,x101,x102,x103,x104,x105,x106,r_x107) = digits9_np8(half,ref norm,q);
    let (a,b) = center_pair_zq(r_x98,r_x107);
    norm += a * a;
    norm += b * b;
    let x98: felt252 = r_x98.into();
    let x107: felt252 = r_x107.into();
    let (high,low) = match u128s_from_felt252(f6) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return None; },
    };
    let (x108,x109,x110,x111,x112,x113,x114,x115,r_x116) = digits9_np8(half,ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return None; },
    };
    let (x117,x118,x119,x120,x121,x122,x123,x124,r_x125) = digits9_np8(half,ref norm,q);
    let (a,b) = center_pair_zq(r_x116,r_x125);
    norm += a * a;
    norm += b * b;
    let x116: felt252 = r_x116.into();
    let x125: felt252 = r_x125.into();
    Some([x0 * s,x1 * s,x2 * s,x3 * s,x4 * s,x5 * s,x6 * s,x7 * s,x8 * s,x9 * s,x10 * s,x11 * s,x12 * s,x13 * s,x14 * s,x15 * s,x16 * s,x17 * s,x18 * s,x19 * s,x20 * s,x21 * s,x22 * s,x23 * s,x24 * s,x25 * s,x26 * s,x27 * s,x28 * s,x29 * s,x30 * s,x31 * s,x32 * s,x33 * s,x34 * s,x35 * s,x36 * s,x37 * s,x38 * s,x39 * s,x40 * s,x41 * s,x42 * s,x43 * s,x44 * s,x45 * s,x46 * s,x47 * s,x48 * s,x49 * s,x50 * s,x51 * s,x52 * s,x53 * s,x54 * s,x55 * s,x56 * s,x57 * s,x58 * s,x59 * s,x60 * s,x61 * s,x62 * s,x63 * s,x64 * s,x65 * s,x66 * s,x67 * s,x68 * s,x69 * s,x70 * s,x71 * s,x72 * s,x73 * s,x74 * s,x75 * s,x76 * s,x77 * s,x78 * s,x79 * s,x80 * s,x81 * s,x82 * s,x83 * s,x84 * s,x85 * s,x86 * s,x87 * s,x88 * s,x89 * s,x90 * s,x91 * s,x92 * s,x93 * s,x94 * s,x95 * s,x96 * s,x97 * s,x98 * s,x99 * s,x100 * s,x101 * s,x102 * s,x103 * s,x104 * s,x105 * s,x106 * s,x107 * s,x108 * s,x109 * s,x110 * s,x111 * s,x112 * s,x113 * s,x114 * s,x115 * s,x116 * s,x117 * s,x118 * s,x119 * s,x120 * s,x121 * s,x122 * s,x123 * s,x124 * s,x125 * s])
}

/// All-zero digits for a rejected chunk (its verdict is carried by the flag).
const ZERO126: [felt252; 126] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];

/// Seven full slots of the hint (126 digits) for the transform, the centered squares of
/// `msg - t` added to `norm`; digits come back times `s` (see [`verify_tail`]), with a flag
/// that is false on a non-canonical slot.
#[inline(never)]
fn unpack_chunk_ntt_d7(
    f: [felt252; 7],ref msg: Span<u16>,ref norm: felt252,q: NonZero<PackingQ>,s: felt252,
) -> ([felt252; 126],bool) {
    let [f0,f1,f2,f3,f4,f5,f6] = f;
    let [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32,m33,m34,m35,m36,m37,m38,m39,m40,m41,m42,m43,m44,m45,m46,m47,m48,m49,m50,m51,m52,m53,m54,m55,m56,m57,m58,m59,m60,m61,m62,m63,m64,m65,m66,m67,m68,m69,m70,m71,m72,m73,m74,m75,m76,m77,m78,m79,m80,m81,m82,m83,m84,m85,m86,m87,m88,m89,m90,m91,m92,m93,m94,m95,m96,m97,m98,m99,m100,m101,m102,m103,m104,m105,m106,m107,m108,m109,m110,m111,m112,m113,m114,m115,m116,m117,m118,m119,m120,m121,m122,m123,m124,m125] = match msg.multi_pop_front::<126>() {
        Some(b) => (*b).unbox(),
        None => { return (ZERO126,false); },
    };
    let (high,low) = match u128s_from_felt252(f0) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x0,x1,x2,x3,x4,x5,x6,x7,x8) = digits9_d(half,[m0,m1,m2,m3,m4,m5,m6,m7,m8],ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x9,x10,x11,x12,x13,x14,x15,x16,x17) = digits9_d(half,[m9,m10,m11,m12,m13,m14,m15,m16,m17],ref norm,q);
    let (high,low) = match u128s_from_felt252(f1) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x18,x19,x20,x21,x22,x23,x24,x25,x26) = digits9_d(half,[m18,m19,m20,m21,m22,m23,m24,m25,m26],ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x27,x28,x29,x30,x31,x32,x33,x34,x35) = digits9_d(half,[m27,m28,m29,m30,m31,m32,m33,m34,m35],ref norm,q);
    let (high,low) = match u128s_from_felt252(f2) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x36,x37,x38,x39,x40,x41,x42,x43,x44) = digits9_d(half,[m36,m37,m38,m39,m40,m41,m42,m43,m44],ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x45,x46,x47,x48,x49,x50,x51,x52,x53) = digits9_d(half,[m45,m46,m47,m48,m49,m50,m51,m52,m53],ref norm,q);
    let (high,low) = match u128s_from_felt252(f3) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x54,x55,x56,x57,x58,x59,x60,x61,x62) = digits9_d(half,[m54,m55,m56,m57,m58,m59,m60,m61,m62],ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x63,x64,x65,x66,x67,x68,x69,x70,x71) = digits9_d(half,[m63,m64,m65,m66,m67,m68,m69,m70,m71],ref norm,q);
    let (high,low) = match u128s_from_felt252(f4) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x72,x73,x74,x75,x76,x77,x78,x79,x80) = digits9_d(half,[m72,m73,m74,m75,m76,m77,m78,m79,m80],ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x81,x82,x83,x84,x85,x86,x87,x88,x89) = digits9_d(half,[m81,m82,m83,m84,m85,m86,m87,m88,m89],ref norm,q);
    let (high,low) = match u128s_from_felt252(f5) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x90,x91,x92,x93,x94,x95,x96,x97,x98) = digits9_d(half,[m90,m91,m92,m93,m94,m95,m96,m97,m98],ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x99,x100,x101,x102,x103,x104,x105,x106,x107) = digits9_d(half,[m99,m100,m101,m102,m103,m104,m105,m106,m107],ref norm,q);
    let (high,low) = match u128s_from_felt252(f6) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    let half: Acc8 = match downcast(low) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x108,x109,x110,x111,x112,x113,x114,x115,x116) = digits9_d(half,[m108,m109,m110,m111,m112,m113,m114,m115,m116],ref norm,q);
    let half: Acc8 = match downcast(high) {
        Some(v) => v,
        None => { return (ZERO126,false); },
    };
    let (x117,x118,x119,x120,x121,x122,x123,x124,x125) = digits9_d(half,[m117,m118,m119,m120,m121,m122,m123,m124,m125],ref norm,q);
    ([x0 * s,x1 * s,x2 * s,x3 * s,x4 * s,x5 * s,x6 * s,x7 * s,x8 * s,x9 * s,x10 * s,x11 * s,x12 * s,x13 * s,x14 * s,x15 * s,x16 * s,x17 * s,x18 * s,x19 * s,x20 * s,x21 * s,x22 * s,x23 * s,x24 * s,x25 * s,x26 * s,x27 * s,x28 * s,x29 * s,x30 * s,x31 * s,x32 * s,x33 * s,x34 * s,x35 * s,x36 * s,x37 * s,x38 * s,x39 * s,x40 * s,x41 * s,x42 * s,x43 * s,x44 * s,x45 * s,x46 * s,x47 * s,x48 * s,x49 * s,x50 * s,x51 * s,x52 * s,x53 * s,x54 * s,x55 * s,x56 * s,x57 * s,x58 * s,x59 * s,x60 * s,x61 * s,x62 * s,x63 * s,x64 * s,x65 * s,x66 * s,x67 * s,x68 * s,x69 * s,x70 * s,x71 * s,x72 * s,x73 * s,x74 * s,x75 * s,x76 * s,x77 * s,x78 * s,x79 * s,x80 * s,x81 * s,x82 * s,x83 * s,x84 * s,x85 * s,x86 * s,x87 * s,x88 * s,x89 * s,x90 * s,x91 * s,x92 * s,x93 * s,x94 * s,x95 * s,x96 * s,x97 * s,x98 * s,x99 * s,x100 * s,x101 * s,x102 * s,x103 * s,x104 * s,x105 * s,x106 * s,x107 * s,x108 * s,x109 * s,x110 * s,x111 * s,x112 * s,x113 * s,x114 * s,x115 * s,x116 * s,x117 * s,x118 * s,x119 * s,x120 * s,x121 * s,x122 * s,x123 * s,x124 * s,x125 * s],true)
}

/// q^-1 in the field: both transforms run on inputs times q^-1 (see [`verify_tail`]).
const Q_INV: felt252 = 0x590625348ee7b13ed5063a897278482929cf2104a53c8ebd06ba86c7dbd6164;
/// 1479 q^-1: the first-layer twiddle (zeta^256) times q^-1, for inputs 252..503.
const ZETA_Q_INV: felt252 = 0x5280f2a59c8cbdc0b6fc301454e8e5d08ba7c1d6a0dca611dfa0aca711da4b8;

/// Zero as a seven-digit accumulator, for the reject path of the hint's last slot.
const ZERO_ACC7: Acc7 = 0;

/// `(a*b - c) * q^-1` for transform outputs `a`, `c` that already carry the factor q^-1:
/// `a*b - c` is that same field element (see [`hint_quotient_inv`] for the bound argument).
#[inline(always)]
fn scaled_quotient(a: L,b: PackingZq,c: L) -> felt252 {
    let b: felt252 = b.into();
    a.value * b - c.value
}

#[inline(always)]
fn check_half9_zq(value: u128,a: [[L; 3]; 3],c: [[L; 3]; 3],q: NonZero<PackingQ>) -> bool {
    let [t0,t1,t2] = a;
    let [u0,u1,u2] = c;
    let [a0,a1,a2] = t0;
    let [c0,c1,c2] = u0;
    let x: Acc8 = match downcast(value) {
        Some(x) => x,
        None => { return false; },
    };
    let (x,d0) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a0,d0,c0)) {
        return false;
    }
    let (x,d1) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a1,d1,c1)) {
        return false;
    }
    let (x,d2) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a2,d2,c2)) {
        return false;
    }
    let [a3,a4,a5] = t1;
    let [c3,c4,c5] = u1;
    let (x,d3) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a3,d3,c3)) {
        return false;
    }
    let (x,d4) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a4,d4,c4)) {
        return false;
    }
    let (x,d5) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a5,d5,c5)) {
        return false;
    }
    let [a6,a7,a8] = t2;
    let [c6,c7,c8] = u2;
    let (x,d6) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a6,d6,c6)) {
        return false;
    }
    let (x,d7) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a7,d7,c7)) {
        return false;
    }
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a8,x,c8)) {
        return false;
    }
    true
}

/// Fourteen public-key slots against the two transforms (see [`unpack_full_slot_zqc`]): one
/// call per fourteen slots, their coordinates passed as arguments.
#[inline(never)]
fn check_slots14_zq(
    f: [[felt252; 7]; 2],a: [[[[L; 3]; 6]; 7]; 2],c: [[[[L; 3]; 6]; 7]; 2],q: NonZero<PackingQ>,
) -> bool {
    let [fa,fb] = f;
    let [ga,gb] = a;
    let [ha,hb] = c;
    check_slots7_zq(fa,ga,ha,q) && check_slots7_zq(fb,gb,hb,q)
}
#[inline(always)]
fn check_slots7_zq(f: [felt252; 7],a: [[[L; 3]; 6]; 7],c: [[[L; 3]; 6]; 7],q: NonZero<PackingQ>) -> bool {
    let [f0,f1,f2,f3,f4,f5,f6] = f;
    let [a0,a1,a2,a3,a4,a5,a6] = a;
    let [c0,c1,c2,c3,c4,c5,c6] = c;
    check_slot_inl(f0,a0,c0,q)
        && check_slot_inl(f1,a1,c1,q)
        && check_slot_inl(f2,a2,c2,q)
        && check_slot_inl(f3,a3,c3,q)
        && check_slot_inl(f4,a4,c4,q)
        && check_slot_inl(f5,a5,c5,q)
        && check_slot_inl(f6,a6,c6,q)
}#[inline(always)]
fn check_slot_inl(felt: felt252,a: [[L; 3]; 6],c: [[L; 3]; 6],q: NonZero<PackingQ>) -> bool {
    let [a0,a1,a2,a3,a4,a5] = a;
    let [c0,c1,c2,c3,c4,c5] = c;
    let (high,low) = match u128s_from_felt252(felt) {
        U128sFromFelt252Result::Wide(x) => x,
        U128sFromFelt252Result::Narrow(x) => (0,x),
    };
    check_half9_zq(low,[a0,a1,a2],[c0,c1,c2],q) && check_half9_zq(high,[a3,a4,a5],[c3,c4,c5],q)
}

/// The key's last slot (eight coordinates) against the two transforms.
#[inline(never)]
fn check_last_slot_zq(felt: felt252,a: [L; 8],c: [L; 8],q: NonZero<PackingQ>) -> bool {
    let [a0,a1,a2,a3,a4,a5,a6,a7] = a;
    let [c0,c1,c2,c3,c4,c5,c6,c7] = c;
    let low = match u128s_from_felt252(felt) {
        U128sFromFelt252Result::Narrow(x) => x,
        U128sFromFelt252Result::Wide(_) => { return false; },
    };
    let x: Acc7 = match downcast(low) {
        Some(x) => x,
        None => { return false; },
    };
    let (x,d0) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a0,d0,c0)) {
        return false;
    }
    let (x,d1) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a1,d1,c1)) {
        return false;
    }
    let (x,d2) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a2,d2,c2)) {
        return false;
    }
    let (x,d3) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a3,d3,c3)) {
        return false;
    }
    let (x,d4) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a4,d4,c4)) {
        return false;
    }
    let (x,d5) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a5,d5,c5)) {
        return false;
    }
    let (x,d6) = bounded_int_div_rem(x,q);
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a6,d6,c6)) {
        return false;
    }
    if let U128sFromFelt252Result::Wide(_) = u128s_from_felt252(scaled_quotient(a7,x,c7)) {
        return false;
    }
    true
}

/// Everything after the hash: s1 and t unpacked into their lazy transforms (both scaled by
/// q^-1, see [`scaled_quotient`]), the norm bound,
/// and each public-key slot checked against both transforms. The transforms stay on the
/// stack (no output boxes to write and read back) and reach the key check as arguments of
/// [`check_slot_zq`]. Once the s1 digits exist, a reject only clears `ok` (no early exit has
/// to drop what is live). Same verdicts as `unpack_ntt_512_n`, `unpack_ntt_512_d`, the bound
/// and `unpack_512_zq_check` in sequence.
#[inline(never)]
pub(crate) fn verify_tail(
    s1_slots: @Box<[felt252; 29]>,t_slots: @Box<[felt252; 29]>,mut msg: Span<u16>,
    mut public_key: Span<felt252>,
) -> bool {
    // An unknown ap change for this function: the caller then keeps what it needs afterwards
    // in locals instead of ap cells further away than an offset can reach across this
    // function's stack.
    core::internal::revoke_ap_tracking();
    let q = packing_q_cell();
    let mut norm_n: felt252 = 0;
    let [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28] = (*s1_slots).unbox();
    // Chunks 2 and 3 hold the transform's inputs 252..503: their digits come back times 1479 q^-1.
    let x0 = match unpack_chunk_ntt_n7([s0,s1,s2,s3,s4,s5,s6],ref norm_n,q,Q_INV) {
        Some(v) => v,
        None => { return false; },
    };
    let x1 = match unpack_chunk_ntt_n7([s7,s8,s9,s10,s11,s12,s13],ref norm_n,q,Q_INV) {
        Some(v) => v,
        None => { return false; },
    };
    let x2 = match unpack_chunk_ntt_n7([s14,s15,s16,s17,s18,s19,s20],ref norm_n,q,ZETA_Q_INV) {
        Some(v) => v,
        None => { return false; },
    };
    let x3 = match unpack_chunk_ntt_n7([s21,s22,s23,s24,s25,s26,s27],ref norm_n,q,ZETA_Q_INV) {
        Some(v) => v,
        None => { return false; },
    };
    let low = match u128s_from_felt252(s28) {
        U128sFromFelt252Result::Narrow(x) => x,
        U128sFromFelt252Result::Wide(_) => { return false; },
    };
    let value: Acc7 = match downcast(low) {
        Some(v) => v,
        None => { return false; },
    };
    let (e0,e1,e2,e3,e4,e5,e6,e7) = digits8_np(value,ref norm_n,q);
    // From here a reject only clears `ok`.
    let mut ok = true;
    let q = packing_q_cell();
    let mut norm_d: felt252 = 0;
    let [t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28] = (*t_slots).unbox();
    let (y0,ok0) = unpack_chunk_ntt_d7([t0,t1,t2,t3,t4,t5,t6],ref msg,ref norm_d,q,Q_INV);
    let (y1,ok1) = unpack_chunk_ntt_d7([t7,t8,t9,t10,t11,t12,t13],ref msg,ref norm_d,q,Q_INV);
    let (y2,ok2) = unpack_chunk_ntt_d7([t14,t15,t16,t17,t18,t19,t20],ref msg,ref norm_d,q,ZETA_Q_INV);
    let (y3,ok3) = unpack_chunk_ntt_d7([t21,t22,t23,t24,t25,t26,t27],ref msg,ref norm_d,q,ZETA_Q_INV);
    ok = ok & ok0 & ok1 & ok2 & ok3;
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
    let [m0,m1,m2,m3,m4,m5,m6,m7] = match msg.multi_pop_front::<8>() {
        Some(b) => (*b).unbox(),
        None => {
            ok = false;
            [0,0,0,0,0,0,0,0]
        },
    };
    let (te0,te1,te2,te3,te4,te5,te6,te7) = digits8_d(value,[m0,m1,m2,m3,m4,m5,m6,m7],ref norm_d,q);
    let (sa,sb) = pqbench_ntt::falcon512_fast::ntt_falcon512_fast_lazy_slots(
        [x0,x1,x2,x3],[e0,e1,e2,e3,e4,e5,e6,e7],0,Q_INV,ZETA_Q_INV,
    );
    let (ta,tb) = pqbench_ntt::falcon512_fast::ntt_falcon512_fast_lazy_slots(
        [y0,y1,y2,y3],[te0,te1,te2,te3,te4,te5,te6,te7],
        crate::falcon::HINT_NTT_OFFSET,Q_INV,ZETA_Q_INV,
    );
    let bound: Option<corelib_imports::bounded_int::BoundedInt<0,34034726>> = downcast(
        norm_n + norm_d,
    );
    if bound.is_none() {
        ok = false;
    }
    let [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27] = sa;
    let [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27] = ta;
    let q = packing_q_cell();
    let [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28] = match public_key.multi_pop_front::<29>() {
        Some(b) => (*b).unbox(),
        None => { return false; },
    };
    let [a0_0,a0_1,a0_2,a0_3,a0_4,a0_5,a0_6,a0_7,a0_8,a0_9,a0_10,a0_11,a0_12,a0_13,a0_14,a0_15,a0_16,a0_17] = a0;
    let ga0 = [[a0_0,a0_1,a0_2],[a0_3,a0_4,a0_5],[a0_6,a0_7,a0_8],[a0_9,a0_10,a0_11],[a0_12,a0_13,a0_14],[a0_15,a0_16,a0_17]];
    let [a1_0,a1_1,a1_2,a1_3,a1_4,a1_5,a1_6,a1_7,a1_8,a1_9,a1_10,a1_11,a1_12,a1_13,a1_14,a1_15,a1_16,a1_17] = a1;
    let ga1 = [[a1_0,a1_1,a1_2],[a1_3,a1_4,a1_5],[a1_6,a1_7,a1_8],[a1_9,a1_10,a1_11],[a1_12,a1_13,a1_14],[a1_15,a1_16,a1_17]];
    let [a2_0,a2_1,a2_2,a2_3,a2_4,a2_5,a2_6,a2_7,a2_8,a2_9,a2_10,a2_11,a2_12,a2_13,a2_14,a2_15,a2_16,a2_17] = a2;
    let ga2 = [[a2_0,a2_1,a2_2],[a2_3,a2_4,a2_5],[a2_6,a2_7,a2_8],[a2_9,a2_10,a2_11],[a2_12,a2_13,a2_14],[a2_15,a2_16,a2_17]];
    let [a3_0,a3_1,a3_2,a3_3,a3_4,a3_5,a3_6,a3_7,a3_8,a3_9,a3_10,a3_11,a3_12,a3_13,a3_14,a3_15,a3_16,a3_17] = a3;
    let ga3 = [[a3_0,a3_1,a3_2],[a3_3,a3_4,a3_5],[a3_6,a3_7,a3_8],[a3_9,a3_10,a3_11],[a3_12,a3_13,a3_14],[a3_15,a3_16,a3_17]];
    let [a4_0,a4_1,a4_2,a4_3,a4_4,a4_5,a4_6,a4_7,a4_8,a4_9,a4_10,a4_11,a4_12,a4_13,a4_14,a4_15,a4_16,a4_17] = a4;
    let ga4 = [[a4_0,a4_1,a4_2],[a4_3,a4_4,a4_5],[a4_6,a4_7,a4_8],[a4_9,a4_10,a4_11],[a4_12,a4_13,a4_14],[a4_15,a4_16,a4_17]];
    let [a5_0,a5_1,a5_2,a5_3,a5_4,a5_5,a5_6,a5_7,a5_8,a5_9,a5_10,a5_11,a5_12,a5_13,a5_14,a5_15,a5_16,a5_17] = a5;
    let ga5 = [[a5_0,a5_1,a5_2],[a5_3,a5_4,a5_5],[a5_6,a5_7,a5_8],[a5_9,a5_10,a5_11],[a5_12,a5_13,a5_14],[a5_15,a5_16,a5_17]];
    let [a6_0,a6_1,a6_2,a6_3,a6_4,a6_5,a6_6,a6_7,a6_8,a6_9,a6_10,a6_11,a6_12,a6_13,a6_14,a6_15,a6_16,a6_17] = a6;
    let ga6 = [[a6_0,a6_1,a6_2],[a6_3,a6_4,a6_5],[a6_6,a6_7,a6_8],[a6_9,a6_10,a6_11],[a6_12,a6_13,a6_14],[a6_15,a6_16,a6_17]];
    let [a7_0,a7_1,a7_2,a7_3,a7_4,a7_5,a7_6,a7_7,a7_8,a7_9,a7_10,a7_11,a7_12,a7_13,a7_14,a7_15,a7_16,a7_17] = a7;
    let ga7 = [[a7_0,a7_1,a7_2],[a7_3,a7_4,a7_5],[a7_6,a7_7,a7_8],[a7_9,a7_10,a7_11],[a7_12,a7_13,a7_14],[a7_15,a7_16,a7_17]];
    let [a8_0,a8_1,a8_2,a8_3,a8_4,a8_5,a8_6,a8_7,a8_8,a8_9,a8_10,a8_11,a8_12,a8_13,a8_14,a8_15,a8_16,a8_17] = a8;
    let ga8 = [[a8_0,a8_1,a8_2],[a8_3,a8_4,a8_5],[a8_6,a8_7,a8_8],[a8_9,a8_10,a8_11],[a8_12,a8_13,a8_14],[a8_15,a8_16,a8_17]];
    let [a9_0,a9_1,a9_2,a9_3,a9_4,a9_5,a9_6,a9_7,a9_8,a9_9,a9_10,a9_11,a9_12,a9_13,a9_14,a9_15,a9_16,a9_17] = a9;
    let ga9 = [[a9_0,a9_1,a9_2],[a9_3,a9_4,a9_5],[a9_6,a9_7,a9_8],[a9_9,a9_10,a9_11],[a9_12,a9_13,a9_14],[a9_15,a9_16,a9_17]];
    let [a10_0,a10_1,a10_2,a10_3,a10_4,a10_5,a10_6,a10_7,a10_8,a10_9,a10_10,a10_11,a10_12,a10_13,a10_14,a10_15,a10_16,a10_17] = a10;
    let ga10 = [[a10_0,a10_1,a10_2],[a10_3,a10_4,a10_5],[a10_6,a10_7,a10_8],[a10_9,a10_10,a10_11],[a10_12,a10_13,a10_14],[a10_15,a10_16,a10_17]];
    let [a11_0,a11_1,a11_2,a11_3,a11_4,a11_5,a11_6,a11_7,a11_8,a11_9,a11_10,a11_11,a11_12,a11_13,a11_14,a11_15,a11_16,a11_17] = a11;
    let ga11 = [[a11_0,a11_1,a11_2],[a11_3,a11_4,a11_5],[a11_6,a11_7,a11_8],[a11_9,a11_10,a11_11],[a11_12,a11_13,a11_14],[a11_15,a11_16,a11_17]];
    let [a12_0,a12_1,a12_2,a12_3,a12_4,a12_5,a12_6,a12_7,a12_8,a12_9,a12_10,a12_11,a12_12,a12_13,a12_14,a12_15,a12_16,a12_17] = a12;
    let ga12 = [[a12_0,a12_1,a12_2],[a12_3,a12_4,a12_5],[a12_6,a12_7,a12_8],[a12_9,a12_10,a12_11],[a12_12,a12_13,a12_14],[a12_15,a12_16,a12_17]];
    let [a13_0,a13_1,a13_2,a13_3,a13_4,a13_5,a13_6,a13_7,a13_8,a13_9,a13_10,a13_11,a13_12,a13_13,a13_14,a13_15,a13_16,a13_17] = a13;
    let ga13 = [[a13_0,a13_1,a13_2],[a13_3,a13_4,a13_5],[a13_6,a13_7,a13_8],[a13_9,a13_10,a13_11],[a13_12,a13_13,a13_14],[a13_15,a13_16,a13_17]];
    let [a14_0,a14_1,a14_2,a14_3,a14_4,a14_5,a14_6,a14_7,a14_8,a14_9,a14_10,a14_11,a14_12,a14_13,a14_14,a14_15,a14_16,a14_17] = a14;
    let ga14 = [[a14_0,a14_1,a14_2],[a14_3,a14_4,a14_5],[a14_6,a14_7,a14_8],[a14_9,a14_10,a14_11],[a14_12,a14_13,a14_14],[a14_15,a14_16,a14_17]];
    let [a15_0,a15_1,a15_2,a15_3,a15_4,a15_5,a15_6,a15_7,a15_8,a15_9,a15_10,a15_11,a15_12,a15_13,a15_14,a15_15,a15_16,a15_17] = a15;
    let ga15 = [[a15_0,a15_1,a15_2],[a15_3,a15_4,a15_5],[a15_6,a15_7,a15_8],[a15_9,a15_10,a15_11],[a15_12,a15_13,a15_14],[a15_15,a15_16,a15_17]];
    let [a16_0,a16_1,a16_2,a16_3,a16_4,a16_5,a16_6,a16_7,a16_8,a16_9,a16_10,a16_11,a16_12,a16_13,a16_14,a16_15,a16_16,a16_17] = a16;
    let ga16 = [[a16_0,a16_1,a16_2],[a16_3,a16_4,a16_5],[a16_6,a16_7,a16_8],[a16_9,a16_10,a16_11],[a16_12,a16_13,a16_14],[a16_15,a16_16,a16_17]];
    let [a17_0,a17_1,a17_2,a17_3,a17_4,a17_5,a17_6,a17_7,a17_8,a17_9,a17_10,a17_11,a17_12,a17_13,a17_14,a17_15,a17_16,a17_17] = a17;
    let ga17 = [[a17_0,a17_1,a17_2],[a17_3,a17_4,a17_5],[a17_6,a17_7,a17_8],[a17_9,a17_10,a17_11],[a17_12,a17_13,a17_14],[a17_15,a17_16,a17_17]];
    let [a18_0,a18_1,a18_2,a18_3,a18_4,a18_5,a18_6,a18_7,a18_8,a18_9,a18_10,a18_11,a18_12,a18_13,a18_14,a18_15,a18_16,a18_17] = a18;
    let ga18 = [[a18_0,a18_1,a18_2],[a18_3,a18_4,a18_5],[a18_6,a18_7,a18_8],[a18_9,a18_10,a18_11],[a18_12,a18_13,a18_14],[a18_15,a18_16,a18_17]];
    let [a19_0,a19_1,a19_2,a19_3,a19_4,a19_5,a19_6,a19_7,a19_8,a19_9,a19_10,a19_11,a19_12,a19_13,a19_14,a19_15,a19_16,a19_17] = a19;
    let ga19 = [[a19_0,a19_1,a19_2],[a19_3,a19_4,a19_5],[a19_6,a19_7,a19_8],[a19_9,a19_10,a19_11],[a19_12,a19_13,a19_14],[a19_15,a19_16,a19_17]];
    let [a20_0,a20_1,a20_2,a20_3,a20_4,a20_5,a20_6,a20_7,a20_8,a20_9,a20_10,a20_11,a20_12,a20_13,a20_14,a20_15,a20_16,a20_17] = a20;
    let ga20 = [[a20_0,a20_1,a20_2],[a20_3,a20_4,a20_5],[a20_6,a20_7,a20_8],[a20_9,a20_10,a20_11],[a20_12,a20_13,a20_14],[a20_15,a20_16,a20_17]];
    let [a21_0,a21_1,a21_2,a21_3,a21_4,a21_5,a21_6,a21_7,a21_8,a21_9,a21_10,a21_11,a21_12,a21_13,a21_14,a21_15,a21_16,a21_17] = a21;
    let ga21 = [[a21_0,a21_1,a21_2],[a21_3,a21_4,a21_5],[a21_6,a21_7,a21_8],[a21_9,a21_10,a21_11],[a21_12,a21_13,a21_14],[a21_15,a21_16,a21_17]];
    let [a22_0,a22_1,a22_2,a22_3,a22_4,a22_5,a22_6,a22_7,a22_8,a22_9,a22_10,a22_11,a22_12,a22_13,a22_14,a22_15,a22_16,a22_17] = a22;
    let ga22 = [[a22_0,a22_1,a22_2],[a22_3,a22_4,a22_5],[a22_6,a22_7,a22_8],[a22_9,a22_10,a22_11],[a22_12,a22_13,a22_14],[a22_15,a22_16,a22_17]];
    let [a23_0,a23_1,a23_2,a23_3,a23_4,a23_5,a23_6,a23_7,a23_8,a23_9,a23_10,a23_11,a23_12,a23_13,a23_14,a23_15,a23_16,a23_17] = a23;
    let ga23 = [[a23_0,a23_1,a23_2],[a23_3,a23_4,a23_5],[a23_6,a23_7,a23_8],[a23_9,a23_10,a23_11],[a23_12,a23_13,a23_14],[a23_15,a23_16,a23_17]];
    let [a24_0,a24_1,a24_2,a24_3,a24_4,a24_5,a24_6,a24_7,a24_8,a24_9,a24_10,a24_11,a24_12,a24_13,a24_14,a24_15,a24_16,a24_17] = a24;
    let ga24 = [[a24_0,a24_1,a24_2],[a24_3,a24_4,a24_5],[a24_6,a24_7,a24_8],[a24_9,a24_10,a24_11],[a24_12,a24_13,a24_14],[a24_15,a24_16,a24_17]];
    let [a25_0,a25_1,a25_2,a25_3,a25_4,a25_5,a25_6,a25_7,a25_8,a25_9,a25_10,a25_11,a25_12,a25_13,a25_14,a25_15,a25_16,a25_17] = a25;
    let ga25 = [[a25_0,a25_1,a25_2],[a25_3,a25_4,a25_5],[a25_6,a25_7,a25_8],[a25_9,a25_10,a25_11],[a25_12,a25_13,a25_14],[a25_15,a25_16,a25_17]];
    let [a26_0,a26_1,a26_2,a26_3,a26_4,a26_5,a26_6,a26_7,a26_8,a26_9,a26_10,a26_11,a26_12,a26_13,a26_14,a26_15,a26_16,a26_17] = a26;
    let ga26 = [[a26_0,a26_1,a26_2],[a26_3,a26_4,a26_5],[a26_6,a26_7,a26_8],[a26_9,a26_10,a26_11],[a26_12,a26_13,a26_14],[a26_15,a26_16,a26_17]];
    let [a27_0,a27_1,a27_2,a27_3,a27_4,a27_5,a27_6,a27_7,a27_8,a27_9,a27_10,a27_11,a27_12,a27_13,a27_14,a27_15,a27_16,a27_17] = a27;
    let ga27 = [[a27_0,a27_1,a27_2],[a27_3,a27_4,a27_5],[a27_6,a27_7,a27_8],[a27_9,a27_10,a27_11],[a27_12,a27_13,a27_14],[a27_15,a27_16,a27_17]];
    let [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c0_10,c0_11,c0_12,c0_13,c0_14,c0_15,c0_16,c0_17] = c0;
    let gc0 = [[c0_0,c0_1,c0_2],[c0_3,c0_4,c0_5],[c0_6,c0_7,c0_8],[c0_9,c0_10,c0_11],[c0_12,c0_13,c0_14],[c0_15,c0_16,c0_17]];
    let [c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c1_8,c1_9,c1_10,c1_11,c1_12,c1_13,c1_14,c1_15,c1_16,c1_17] = c1;
    let gc1 = [[c1_0,c1_1,c1_2],[c1_3,c1_4,c1_5],[c1_6,c1_7,c1_8],[c1_9,c1_10,c1_11],[c1_12,c1_13,c1_14],[c1_15,c1_16,c1_17]];
    let [c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17] = c2;
    let gc2 = [[c2_0,c2_1,c2_2],[c2_3,c2_4,c2_5],[c2_6,c2_7,c2_8],[c2_9,c2_10,c2_11],[c2_12,c2_13,c2_14],[c2_15,c2_16,c2_17]];
    let [c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17] = c3;
    let gc3 = [[c3_0,c3_1,c3_2],[c3_3,c3_4,c3_5],[c3_6,c3_7,c3_8],[c3_9,c3_10,c3_11],[c3_12,c3_13,c3_14],[c3_15,c3_16,c3_17]];
    let [c4_0,c4_1,c4_2,c4_3,c4_4,c4_5,c4_6,c4_7,c4_8,c4_9,c4_10,c4_11,c4_12,c4_13,c4_14,c4_15,c4_16,c4_17] = c4;
    let gc4 = [[c4_0,c4_1,c4_2],[c4_3,c4_4,c4_5],[c4_6,c4_7,c4_8],[c4_9,c4_10,c4_11],[c4_12,c4_13,c4_14],[c4_15,c4_16,c4_17]];
    let [c5_0,c5_1,c5_2,c5_3,c5_4,c5_5,c5_6,c5_7,c5_8,c5_9,c5_10,c5_11,c5_12,c5_13,c5_14,c5_15,c5_16,c5_17] = c5;
    let gc5 = [[c5_0,c5_1,c5_2],[c5_3,c5_4,c5_5],[c5_6,c5_7,c5_8],[c5_9,c5_10,c5_11],[c5_12,c5_13,c5_14],[c5_15,c5_16,c5_17]];
    let [c6_0,c6_1,c6_2,c6_3,c6_4,c6_5,c6_6,c6_7,c6_8,c6_9,c6_10,c6_11,c6_12,c6_13,c6_14,c6_15,c6_16,c6_17] = c6;
    let gc6 = [[c6_0,c6_1,c6_2],[c6_3,c6_4,c6_5],[c6_6,c6_7,c6_8],[c6_9,c6_10,c6_11],[c6_12,c6_13,c6_14],[c6_15,c6_16,c6_17]];
    let [c7_0,c7_1,c7_2,c7_3,c7_4,c7_5,c7_6,c7_7,c7_8,c7_9,c7_10,c7_11,c7_12,c7_13,c7_14,c7_15,c7_16,c7_17] = c7;
    let gc7 = [[c7_0,c7_1,c7_2],[c7_3,c7_4,c7_5],[c7_6,c7_7,c7_8],[c7_9,c7_10,c7_11],[c7_12,c7_13,c7_14],[c7_15,c7_16,c7_17]];
    let [c8_0,c8_1,c8_2,c8_3,c8_4,c8_5,c8_6,c8_7,c8_8,c8_9,c8_10,c8_11,c8_12,c8_13,c8_14,c8_15,c8_16,c8_17] = c8;
    let gc8 = [[c8_0,c8_1,c8_2],[c8_3,c8_4,c8_5],[c8_6,c8_7,c8_8],[c8_9,c8_10,c8_11],[c8_12,c8_13,c8_14],[c8_15,c8_16,c8_17]];
    let [c9_0,c9_1,c9_2,c9_3,c9_4,c9_5,c9_6,c9_7,c9_8,c9_9,c9_10,c9_11,c9_12,c9_13,c9_14,c9_15,c9_16,c9_17] = c9;
    let gc9 = [[c9_0,c9_1,c9_2],[c9_3,c9_4,c9_5],[c9_6,c9_7,c9_8],[c9_9,c9_10,c9_11],[c9_12,c9_13,c9_14],[c9_15,c9_16,c9_17]];
    let [c10_0,c10_1,c10_2,c10_3,c10_4,c10_5,c10_6,c10_7,c10_8,c10_9,c10_10,c10_11,c10_12,c10_13,c10_14,c10_15,c10_16,c10_17] = c10;
    let gc10 = [[c10_0,c10_1,c10_2],[c10_3,c10_4,c10_5],[c10_6,c10_7,c10_8],[c10_9,c10_10,c10_11],[c10_12,c10_13,c10_14],[c10_15,c10_16,c10_17]];
    let [c11_0,c11_1,c11_2,c11_3,c11_4,c11_5,c11_6,c11_7,c11_8,c11_9,c11_10,c11_11,c11_12,c11_13,c11_14,c11_15,c11_16,c11_17] = c11;
    let gc11 = [[c11_0,c11_1,c11_2],[c11_3,c11_4,c11_5],[c11_6,c11_7,c11_8],[c11_9,c11_10,c11_11],[c11_12,c11_13,c11_14],[c11_15,c11_16,c11_17]];
    let [c12_0,c12_1,c12_2,c12_3,c12_4,c12_5,c12_6,c12_7,c12_8,c12_9,c12_10,c12_11,c12_12,c12_13,c12_14,c12_15,c12_16,c12_17] = c12;
    let gc12 = [[c12_0,c12_1,c12_2],[c12_3,c12_4,c12_5],[c12_6,c12_7,c12_8],[c12_9,c12_10,c12_11],[c12_12,c12_13,c12_14],[c12_15,c12_16,c12_17]];
    let [c13_0,c13_1,c13_2,c13_3,c13_4,c13_5,c13_6,c13_7,c13_8,c13_9,c13_10,c13_11,c13_12,c13_13,c13_14,c13_15,c13_16,c13_17] = c13;
    let gc13 = [[c13_0,c13_1,c13_2],[c13_3,c13_4,c13_5],[c13_6,c13_7,c13_8],[c13_9,c13_10,c13_11],[c13_12,c13_13,c13_14],[c13_15,c13_16,c13_17]];
    let [c14_0,c14_1,c14_2,c14_3,c14_4,c14_5,c14_6,c14_7,c14_8,c14_9,c14_10,c14_11,c14_12,c14_13,c14_14,c14_15,c14_16,c14_17] = c14;
    let gc14 = [[c14_0,c14_1,c14_2],[c14_3,c14_4,c14_5],[c14_6,c14_7,c14_8],[c14_9,c14_10,c14_11],[c14_12,c14_13,c14_14],[c14_15,c14_16,c14_17]];
    let [c15_0,c15_1,c15_2,c15_3,c15_4,c15_5,c15_6,c15_7,c15_8,c15_9,c15_10,c15_11,c15_12,c15_13,c15_14,c15_15,c15_16,c15_17] = c15;
    let gc15 = [[c15_0,c15_1,c15_2],[c15_3,c15_4,c15_5],[c15_6,c15_7,c15_8],[c15_9,c15_10,c15_11],[c15_12,c15_13,c15_14],[c15_15,c15_16,c15_17]];
    let [c16_0,c16_1,c16_2,c16_3,c16_4,c16_5,c16_6,c16_7,c16_8,c16_9,c16_10,c16_11,c16_12,c16_13,c16_14,c16_15,c16_16,c16_17] = c16;
    let gc16 = [[c16_0,c16_1,c16_2],[c16_3,c16_4,c16_5],[c16_6,c16_7,c16_8],[c16_9,c16_10,c16_11],[c16_12,c16_13,c16_14],[c16_15,c16_16,c16_17]];
    let [c17_0,c17_1,c17_2,c17_3,c17_4,c17_5,c17_6,c17_7,c17_8,c17_9,c17_10,c17_11,c17_12,c17_13,c17_14,c17_15,c17_16,c17_17] = c17;
    let gc17 = [[c17_0,c17_1,c17_2],[c17_3,c17_4,c17_5],[c17_6,c17_7,c17_8],[c17_9,c17_10,c17_11],[c17_12,c17_13,c17_14],[c17_15,c17_16,c17_17]];
    let [c18_0,c18_1,c18_2,c18_3,c18_4,c18_5,c18_6,c18_7,c18_8,c18_9,c18_10,c18_11,c18_12,c18_13,c18_14,c18_15,c18_16,c18_17] = c18;
    let gc18 = [[c18_0,c18_1,c18_2],[c18_3,c18_4,c18_5],[c18_6,c18_7,c18_8],[c18_9,c18_10,c18_11],[c18_12,c18_13,c18_14],[c18_15,c18_16,c18_17]];
    let [c19_0,c19_1,c19_2,c19_3,c19_4,c19_5,c19_6,c19_7,c19_8,c19_9,c19_10,c19_11,c19_12,c19_13,c19_14,c19_15,c19_16,c19_17] = c19;
    let gc19 = [[c19_0,c19_1,c19_2],[c19_3,c19_4,c19_5],[c19_6,c19_7,c19_8],[c19_9,c19_10,c19_11],[c19_12,c19_13,c19_14],[c19_15,c19_16,c19_17]];
    let [c20_0,c20_1,c20_2,c20_3,c20_4,c20_5,c20_6,c20_7,c20_8,c20_9,c20_10,c20_11,c20_12,c20_13,c20_14,c20_15,c20_16,c20_17] = c20;
    let gc20 = [[c20_0,c20_1,c20_2],[c20_3,c20_4,c20_5],[c20_6,c20_7,c20_8],[c20_9,c20_10,c20_11],[c20_12,c20_13,c20_14],[c20_15,c20_16,c20_17]];
    let [c21_0,c21_1,c21_2,c21_3,c21_4,c21_5,c21_6,c21_7,c21_8,c21_9,c21_10,c21_11,c21_12,c21_13,c21_14,c21_15,c21_16,c21_17] = c21;
    let gc21 = [[c21_0,c21_1,c21_2],[c21_3,c21_4,c21_5],[c21_6,c21_7,c21_8],[c21_9,c21_10,c21_11],[c21_12,c21_13,c21_14],[c21_15,c21_16,c21_17]];
    let [c22_0,c22_1,c22_2,c22_3,c22_4,c22_5,c22_6,c22_7,c22_8,c22_9,c22_10,c22_11,c22_12,c22_13,c22_14,c22_15,c22_16,c22_17] = c22;
    let gc22 = [[c22_0,c22_1,c22_2],[c22_3,c22_4,c22_5],[c22_6,c22_7,c22_8],[c22_9,c22_10,c22_11],[c22_12,c22_13,c22_14],[c22_15,c22_16,c22_17]];
    let [c23_0,c23_1,c23_2,c23_3,c23_4,c23_5,c23_6,c23_7,c23_8,c23_9,c23_10,c23_11,c23_12,c23_13,c23_14,c23_15,c23_16,c23_17] = c23;
    let gc23 = [[c23_0,c23_1,c23_2],[c23_3,c23_4,c23_5],[c23_6,c23_7,c23_8],[c23_9,c23_10,c23_11],[c23_12,c23_13,c23_14],[c23_15,c23_16,c23_17]];
    let [c24_0,c24_1,c24_2,c24_3,c24_4,c24_5,c24_6,c24_7,c24_8,c24_9,c24_10,c24_11,c24_12,c24_13,c24_14,c24_15,c24_16,c24_17] = c24;
    let gc24 = [[c24_0,c24_1,c24_2],[c24_3,c24_4,c24_5],[c24_6,c24_7,c24_8],[c24_9,c24_10,c24_11],[c24_12,c24_13,c24_14],[c24_15,c24_16,c24_17]];
    let [c25_0,c25_1,c25_2,c25_3,c25_4,c25_5,c25_6,c25_7,c25_8,c25_9,c25_10,c25_11,c25_12,c25_13,c25_14,c25_15,c25_16,c25_17] = c25;
    let gc25 = [[c25_0,c25_1,c25_2],[c25_3,c25_4,c25_5],[c25_6,c25_7,c25_8],[c25_9,c25_10,c25_11],[c25_12,c25_13,c25_14],[c25_15,c25_16,c25_17]];
    let [c26_0,c26_1,c26_2,c26_3,c26_4,c26_5,c26_6,c26_7,c26_8,c26_9,c26_10,c26_11,c26_12,c26_13,c26_14,c26_15,c26_16,c26_17] = c26;
    let gc26 = [[c26_0,c26_1,c26_2],[c26_3,c26_4,c26_5],[c26_6,c26_7,c26_8],[c26_9,c26_10,c26_11],[c26_12,c26_13,c26_14],[c26_15,c26_16,c26_17]];
    let [c27_0,c27_1,c27_2,c27_3,c27_4,c27_5,c27_6,c27_7,c27_8,c27_9,c27_10,c27_11,c27_12,c27_13,c27_14,c27_15,c27_16,c27_17] = c27;
    let gc27 = [[c27_0,c27_1,c27_2],[c27_3,c27_4,c27_5],[c27_6,c27_7,c27_8],[c27_9,c27_10,c27_11],[c27_12,c27_13,c27_14],[c27_15,c27_16,c27_17]];
    ok = ok & check_slots14_zq([[p0,p1,p2,p3,p4,p5,p6],[p7,p8,p9,p10,p11,p12,p13]],[[ga0,ga1,ga2,ga3,ga4,ga5,ga6],[ga7,ga8,ga9,ga10,ga11,ga12,ga13]],[[gc0,gc1,gc2,gc3,gc4,gc5,gc6],[gc7,gc8,gc9,gc10,gc11,gc12,gc13]],q);
    ok = ok & check_slots14_zq([[p14,p15,p16,p17,p18,p19,p20],[p21,p22,p23,p24,p25,p26,p27]],[[ga14,ga15,ga16,ga17,ga18,ga19,ga20],[ga21,ga22,ga23,ga24,ga25,ga26,ga27]],[[gc14,gc15,gc16,gc17,gc18,gc19,gc20],[gc21,gc22,gc23,gc24,gc25,gc26,gc27]],q);
    ok & check_last_slot_zq(p28,sb,tb,q)
}
