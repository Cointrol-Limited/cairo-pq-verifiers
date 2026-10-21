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
use pqbench_ntt::LazyCoeff;
use crate::hashing::hash_to_point::MsgCoeff;
use crate::zq::Q;

/// Coefficients per full felt252 slot (two u128 halves of 9).
pub const VALS_PER_FELT: u32 = 18;
/// felt252 slots for 512 coefficients: 28 full slots + 1 slot with 8.
pub const PACKED_SLOTS: u32 = 29;
/// Coefficients in the last slot: 512 - 28*18.
const LAST_SLOT_VALS: u32 = 8;

const TWO_POW_128: felt252 = 0x100000000000000000000000000000000;

pub(crate) type PackingZq=BoundedInt<0,12288>;
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

#[inline(never)]
fn packing_q_cell()->NonZero<PackingQ> {
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
let q=packing_q_cell();
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
fn unpack_full_slot_u16(felt:felt252,ref coeffs:Array<u16>,q:NonZero<PackingQ>)->bool {
    let value: u256 = felt.into();
unpack_half9_u16(value.low,ref coeffs,q) && unpack_half9_u16(value.high,ref coeffs,q)
}

/// Extract nine base-Q digits from a u128 half. Values below Q^9 are canonical;
/// after eight divisions the remaining quotient is the ninth digit.
#[inline(always)]
fn unpack_half9_u16(value:u128,ref coeffs:Array<u16>,q:NonZero<PackingQ>)->bool {
    let value: Acc8 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
let (rest,d0)=bounded_int_div_rem(value,q);
let (rest,d1)=bounded_int_div_rem(rest,q);
let (rest,d2)=bounded_int_div_rem(rest,q);
let (rest,d3)=bounded_int_div_rem(rest,q);
let (rest,d4)=bounded_int_div_rem(rest,q);
let (rest,d5)=bounded_int_div_rem(rest,q);
let (rest,d6)=bounded_int_div_rem(rest,q);
let (rest,d7)=bounded_int_div_rem(rest,q);
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
fn unpack_half8_u16(value:u128,ref coeffs:Array<u16>,q:NonZero<PackingQ>)->bool {
    let value: Acc7 = match downcast(value) {
        Some(v) => v,
        None => { return false; },
    };
let (rest,d0)=bounded_int_div_rem(value,q);
let (rest,d1)=bounded_int_div_rem(rest,q);
let (rest,d2)=bounded_int_div_rem(rest,q);
let (rest,d3)=bounded_int_div_rem(rest,q);
let (rest,d4)=bounded_int_div_rem(rest,q);
let (rest,d5)=bounded_int_div_rem(rest,q);
let (rest,d6)=bounded_int_div_rem(rest,q);
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
fn unpack_full_slot_zq(felt:felt252,ref coeffs:Array<PackingZq>,q:NonZero<PackingQ>)->bool {
let value:u256=felt.into();
unpack_half9_zq(value.low,ref coeffs,q) && unpack_half9_zq(value.high,ref coeffs,q)
}
#[inline(always)]
fn unpack_half9_zq(value:u128,ref coeffs:Array<PackingZq>,q:NonZero<PackingQ>)->bool {
let value:Acc8=match downcast(value) {
Some(v)=>v,
None=>{ return false; },
};
let (rest,d0)=bounded_int_div_rem(value,q);
let (rest,d1)=bounded_int_div_rem(rest,q);
let (rest,d2)=bounded_int_div_rem(rest,q);
let (rest,d3)=bounded_int_div_rem(rest,q);
let (rest,d4)=bounded_int_div_rem(rest,q);
let (rest,d5)=bounded_int_div_rem(rest,q);
let (rest,d6)=bounded_int_div_rem(rest,q);
let (rest,d7)=bounded_int_div_rem(rest,q);
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
#[inline(always)]
fn unpack_half8_zq(value:u128,ref coeffs:Array<PackingZq>,q:NonZero<PackingQ>)->bool {
let value:Acc7=match downcast(value) {
Some(v)=>v,
None=>{ return false; },
};
let (rest,d0)=bounded_int_div_rem(value,q);
let (rest,d1)=bounded_int_div_rem(rest,q);
let (rest,d2)=bounded_int_div_rem(rest,q);
let (rest,d3)=bounded_int_div_rem(rest,q);
let (rest,d4)=bounded_int_div_rem(rest,q);
let (rest,d5)=bounded_int_div_rem(rest,q);
let (rest,d6)=bounded_int_div_rem(rest,q);
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
type CenterShiftZq=BoundedInt<6144,18432>;
type CenteredZq=BoundedInt<-6144,6144>;
impl AddZqHalf of AddHelper<PackingZq,UnitInt<6144>> {
type Result=CenterShiftZq;
}
impl DivRemCenterShiftZq of DivRemHelper<CenterShiftZq,PackingQ> {
type DivT=BoundedInt<0,1>;
type RemT=PackingZq;
}
impl SubZqHalf of SubHelper<PackingZq,UnitInt<6144>> {
type Result=CenteredZq;
}
impl MulCenteredZq of MulHelper<CenteredZq,CenteredZq> {
type Result=BoundedInt<-37748736,37748736>;
}
impl ConstrainZqHalf of ConstrainHelper<PackingZq,6145> {
type LowT=BoundedInt<0,6144>;
type HighT=BoundedInt<6145,12288>;
}
#[inline(always)]
fn center_sq_zq(d:PackingZq,q:NonZero<PackingQ>)->felt252 {
let x:felt252=match constrain::<PackingZq,6145>(d) {
Ok(low)=>low.into(),
Err(high)=>high.into() - 12289,
};
x * x
}
type DiffShiftZq=BoundedInt<6145,192549956912>;
impl AddU16DiffOffset of AddHelper<MsgCoeff,UnitInt<18433>> {
type Result=BoundedInt<18433,192549956912>;
}
impl SubDiffZq of SubHelper<BoundedInt<18433,192549956912>,PackingZq> {
type Result=DiffShiftZq;
}
impl DivRemDiffShiftZq of DivRemHelper<DiffShiftZq,PackingQ> {
type DivT=BoundedInt<0,15668480>;
type RemT=PackingZq;
}
#[inline(always)]
fn center_diff_sq_zq(m:MsgCoeff,t:PackingZq,q:NonZero<PackingQ>)->felt252 {
let offset:UnitInt<18433> = 18433;
let half:UnitInt<6144> = 6144;
let (_,r)=bounded_int_div_rem(bounded_int::sub(bounded_int::add(m,offset),t),q);
let c=bounded_int::sub(r,half);
bounded_int::mul(c,c).into()
}
#[inline(always)]
fn center_pair_zq(a:PackingZq,b:PackingZq)->(felt252,felt252) {
match constrain::<PackingZq,6145>(a) {
Ok(la)=>match constrain::<PackingZq,6145>(b) {
Ok(lb)=>(la.into(),lb.into()),
Err(hb)=>(la.into(),hb.into() - 12289),
},
Err(ha)=>match constrain::<PackingZq,6145>(b) {
Ok(lb)=>(ha.into() - 12289,lb.into()),
Err(hb)=>(ha.into() - 12289,hb.into() - 12289),
},
}
}
#[inline(always)]
fn digits9_np8(value:Acc8,ref norm:felt252,q:NonZero<PackingQ>)->(felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252,PackingZq) {
let (rest,d0)=bounded_int_div_rem(value,q);
let (rest,d1)=bounded_int_div_rem(rest,q);
let (rest,d2)=bounded_int_div_rem(rest,q);
let (rest,d3)=bounded_int_div_rem(rest,q);
let (rest,d4)=bounded_int_div_rem(rest,q);
let (rest,d5)=bounded_int_div_rem(rest,q);
let (rest,d6)=bounded_int_div_rem(rest,q);
let (rest,d7)=bounded_int_div_rem(rest,q);
let (a,b)=center_pair_zq(d0,d1);
norm += a * a;
norm += b * b;
let (a,b)=center_pair_zq(d2,d3);
norm += a * a;
norm += b * b;
let (a,b)=center_pair_zq(d4,d5);
norm += a * a;
norm += b * b;
let (a,b)=center_pair_zq(d6,d7);
norm += a * a;
norm += b * b;
(d0.into(),d1.into(),d2.into(),d3.into(),d4.into(),d5.into(),d6.into(),d7.into(),rest)
}
#[inline(always)]
fn digits9_d(value:Acc8,m:[MsgCoeff; 9],ref norm:felt252,q:NonZero<PackingQ>)->(felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252) {
let (rest,d0)=bounded_int_div_rem(value,q);
let (rest,d1)=bounded_int_div_rem(rest,q);
let (rest,d2)=bounded_int_div_rem(rest,q);
let (rest,d3)=bounded_int_div_rem(rest,q);
let (rest,d4)=bounded_int_div_rem(rest,q);
let (rest,d5)=bounded_int_div_rem(rest,q);
let (rest,d6)=bounded_int_div_rem(rest,q);
let (rest,d7)=bounded_int_div_rem(rest,q);
let [m0,m1,m2,m3,m4,m5,m6,m7,m8]=m;
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
fn digits8_np(value:Acc7,ref norm:felt252,q:NonZero<PackingQ>)->(felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252) {
let (rest,d0)=bounded_int_div_rem(value,q);
let (rest,d1)=bounded_int_div_rem(rest,q);
let (rest,d2)=bounded_int_div_rem(rest,q);
let (rest,d3)=bounded_int_div_rem(rest,q);
let (rest,d4)=bounded_int_div_rem(rest,q);
let (rest,d5)=bounded_int_div_rem(rest,q);
let (rest,d6)=bounded_int_div_rem(rest,q);
let (a,b)=center_pair_zq(d0,d1);
norm += a * a;
norm += b * b;
let (a,b)=center_pair_zq(d2,d3);
norm += a * a;
norm += b * b;
let (a,b)=center_pair_zq(d4,d5);
norm += a * a;
norm += b * b;
let (a,b)=center_pair_zq(d6,rest);
norm += a * a;
norm += b * b;
(d0.into(),d1.into(),d2.into(),d3.into(),d4.into(),d5.into(),d6.into(),rest.into())
}
#[inline(always)]
fn digits8_d(value:Acc7,m:[MsgCoeff; 8],ref norm:felt252,q:NonZero<PackingQ>)->(felt252,felt252,felt252,felt252,felt252,felt252,felt252,felt252) {
let (rest,d0)=bounded_int_div_rem(value,q);
let (rest,d1)=bounded_int_div_rem(rest,q);
let (rest,d2)=bounded_int_div_rem(rest,q);
let (rest,d3)=bounded_int_div_rem(rest,q);
let (rest,d4)=bounded_int_div_rem(rest,q);
let (rest,d5)=bounded_int_div_rem(rest,q);
let (rest,d6)=bounded_int_div_rem(rest,q);
let [m0,m1,m2,m3,m4,m5,m6,m7]=m;
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
#[inline(never)]
fn unpack_chunk_ntt_n7(
f:[felt252; 7],ref norm:felt252,q:NonZero<PackingQ>,s:felt252,
)->Option<[felt252; 126]> {
let [f0,f1,f2,f3,f4,f5,f6]=f;
let (high,low)=match u128s_from_felt252(f0) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ return None; },
};
let (x0,x1,x2,x3,x4,x5,x6,x7,r_x8)=digits9_np8(half,ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ return None; },
};
let (x9,x10,x11,x12,x13,x14,x15,x16,r_x17)=digits9_np8(half,ref norm,q);
let (a,b)=center_pair_zq(r_x8,r_x17);
norm += a * a;
norm += b * b;
let x8:felt252=r_x8.into();
let x17:felt252=r_x17.into();
let (high,low)=match u128s_from_felt252(f1) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ return None; },
};
let (x18,x19,x20,x21,x22,x23,x24,x25,r_x26)=digits9_np8(half,ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ return None; },
};
let (x27,x28,x29,x30,x31,x32,x33,x34,r_x35)=digits9_np8(half,ref norm,q);
let (a,b)=center_pair_zq(r_x26,r_x35);
norm += a * a;
norm += b * b;
let x26:felt252=r_x26.into();
let x35:felt252=r_x35.into();
let (high,low)=match u128s_from_felt252(f2) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ return None; },
};
let (x36,x37,x38,x39,x40,x41,x42,x43,r_x44)=digits9_np8(half,ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ return None; },
};
let (x45,x46,x47,x48,x49,x50,x51,x52,r_x53)=digits9_np8(half,ref norm,q);
let (a,b)=center_pair_zq(r_x44,r_x53);
norm += a * a;
norm += b * b;
let x44:felt252=r_x44.into();
let x53:felt252=r_x53.into();
let (high,low)=match u128s_from_felt252(f3) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ return None; },
};
let (x54,x55,x56,x57,x58,x59,x60,x61,r_x62)=digits9_np8(half,ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ return None; },
};
let (x63,x64,x65,x66,x67,x68,x69,x70,r_x71)=digits9_np8(half,ref norm,q);
let (a,b)=center_pair_zq(r_x62,r_x71);
norm += a * a;
norm += b * b;
let x62:felt252=r_x62.into();
let x71:felt252=r_x71.into();
let (high,low)=match u128s_from_felt252(f4) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ return None; },
};
let (x72,x73,x74,x75,x76,x77,x78,x79,r_x80)=digits9_np8(half,ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ return None; },
};
let (x81,x82,x83,x84,x85,x86,x87,x88,r_x89)=digits9_np8(half,ref norm,q);
let (a,b)=center_pair_zq(r_x80,r_x89);
norm += a * a;
norm += b * b;
let x80:felt252=r_x80.into();
let x89:felt252=r_x89.into();
let (high,low)=match u128s_from_felt252(f5) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ return None; },
};
let (x90,x91,x92,x93,x94,x95,x96,x97,r_x98)=digits9_np8(half,ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ return None; },
};
let (x99,x100,x101,x102,x103,x104,x105,x106,r_x107)=digits9_np8(half,ref norm,q);
let (a,b)=center_pair_zq(r_x98,r_x107);
norm += a * a;
norm += b * b;
let x98:felt252=r_x98.into();
let x107:felt252=r_x107.into();
let (high,low)=match u128s_from_felt252(f6) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ return None; },
};
let (x108,x109,x110,x111,x112,x113,x114,x115,r_x116)=digits9_np8(half,ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ return None; },
};
let (x117,x118,x119,x120,x121,x122,x123,x124,r_x125)=digits9_np8(half,ref norm,q);
let (a,b)=center_pair_zq(r_x116,r_x125);
norm += a * a;
norm += b * b;
let x116:felt252=r_x116.into();
let x125:felt252=r_x125.into();
Some([x0 * s,x1 * s,x2 * s,x3 * s,x4 * s,x5 * s,x6 * s,x7 * s,x8 * s,x9 * s,x10 * s,x11 * s,x12 * s,x13 * s,x14 * s,x15 * s,x16 * s,x17 * s,x18 * s,x19 * s,x20 * s,x21 * s,x22 * s,x23 * s,x24 * s,x25 * s,x26 * s,x27 * s,x28 * s,x29 * s,x30 * s,x31 * s,x32 * s,x33 * s,x34 * s,x35 * s,x36 * s,x37 * s,x38 * s,x39 * s,x40 * s,x41 * s,x42 * s,x43 * s,x44 * s,x45 * s,x46 * s,x47 * s,x48 * s,x49 * s,x50 * s,x51 * s,x52 * s,x53 * s,x54 * s,x55 * s,x56 * s,x57 * s,x58 * s,x59 * s,x60 * s,x61 * s,x62 * s,x63 * s,x64 * s,x65 * s,x66 * s,x67 * s,x68 * s,x69 * s,x70 * s,x71 * s,x72 * s,x73 * s,x74 * s,x75 * s,x76 * s,x77 * s,x78 * s,x79 * s,x80 * s,x81 * s,x82 * s,x83 * s,x84 * s,x85 * s,x86 * s,x87 * s,x88 * s,x89 * s,x90 * s,x91 * s,x92 * s,x93 * s,x94 * s,x95 * s,x96 * s,x97 * s,x98 * s,x99 * s,x100 * s,x101 * s,x102 * s,x103 * s,x104 * s,x105 * s,x106 * s,x107 * s,x108 * s,x109 * s,x110 * s,x111 * s,x112 * s,x113 * s,x114 * s,x115 * s,x116 * s,x117 * s,x118 * s,x119 * s,x120 * s,x121 * s,x122 * s,x123 * s,x124 * s,x125 * s])
}
const ZERO126:[felt252; 126]=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
#[inline(never)]
fn unpack_chunk_ntt_d7(
f:[felt252; 7],ref msg:Span<MsgCoeff>,ref norm:felt252,q:NonZero<PackingQ>,s:felt252,
)->[felt252; 126] {
let [f0,f1,f2,f3,f4,f5,f6]=f;
let [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32,m33,m34,m35,m36,m37,m38,m39,m40,m41,m42,m43,m44,m45,m46,m47,m48,m49,m50,m51,m52,m53,m54,m55,m56,m57,m58,m59,m60,m61,m62,m63,m64,m65,m66,m67,m68,m69,m70,m71,m72,m73,m74,m75,m76,m77,m78,m79,m80,m81,m82,m83,m84,m85,m86,m87,m88,m89,m90,m91,m92,m93,m94,m95,m96,m97,m98,m99,m100,m101,m102,m103,m104,m105,m106,m107,m108,m109,m110,m111,m112,m113,m114,m115,m116,m117,m118,m119,m120,m121,m122,m123,m124,m125]=match msg.multi_pop_front::<126>() {
Some(b)=>(*b).unbox(),
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (high,low)=match u128s_from_felt252(f0) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x0,x1,x2,x3,x4,x5,x6,x7,x8)=digits9_d(half,[m0,m1,m2,m3,m4,m5,m6,m7,m8],ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x9,x10,x11,x12,x13,x14,x15,x16,x17)=digits9_d(half,[m9,m10,m11,m12,m13,m14,m15,m16,m17],ref norm,q);
let (high,low)=match u128s_from_felt252(f1) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x18,x19,x20,x21,x22,x23,x24,x25,x26)=digits9_d(half,[m18,m19,m20,m21,m22,m23,m24,m25,m26],ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x27,x28,x29,x30,x31,x32,x33,x34,x35)=digits9_d(half,[m27,m28,m29,m30,m31,m32,m33,m34,m35],ref norm,q);
let (high,low)=match u128s_from_felt252(f2) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x36,x37,x38,x39,x40,x41,x42,x43,x44)=digits9_d(half,[m36,m37,m38,m39,m40,m41,m42,m43,m44],ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x45,x46,x47,x48,x49,x50,x51,x52,x53)=digits9_d(half,[m45,m46,m47,m48,m49,m50,m51,m52,m53],ref norm,q);
let (high,low)=match u128s_from_felt252(f3) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x54,x55,x56,x57,x58,x59,x60,x61,x62)=digits9_d(half,[m54,m55,m56,m57,m58,m59,m60,m61,m62],ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x63,x64,x65,x66,x67,x68,x69,x70,x71)=digits9_d(half,[m63,m64,m65,m66,m67,m68,m69,m70,m71],ref norm,q);
let (high,low)=match u128s_from_felt252(f4) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x72,x73,x74,x75,x76,x77,x78,x79,x80)=digits9_d(half,[m72,m73,m74,m75,m76,m77,m78,m79,m80],ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x81,x82,x83,x84,x85,x86,x87,x88,x89)=digits9_d(half,[m81,m82,m83,m84,m85,m86,m87,m88,m89],ref norm,q);
let (high,low)=match u128s_from_felt252(f5) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x90,x91,x92,x93,x94,x95,x96,x97,x98)=digits9_d(half,[m90,m91,m92,m93,m94,m95,m96,m97,m98],ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x99,x100,x101,x102,x103,x104,x105,x106,x107)=digits9_d(half,[m99,m100,m101,m102,m103,m104,m105,m106,m107],ref norm,q);
let (high,low)=match u128s_from_felt252(f6) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
let half:Acc8=match downcast(low) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x108,x109,x110,x111,x112,x113,x114,x115,x116)=digits9_d(half,[m108,m109,m110,m111,m112,m113,m114,m115,m116],ref norm,q);
let half:Acc8=match downcast(high) {
Some(v)=>v,
None=>{ norm += REJECT_NORM;
return ZERO126; },
};
let (x117,x118,x119,x120,x121,x122,x123,x124,x125)=digits9_d(half,[m117,m118,m119,m120,m121,m122,m123,m124,m125],ref norm,q);
[x0 * s,x1 * s,x2 * s,x3 * s,x4 * s,x5 * s,x6 * s,x7 * s,x8 * s,x9 * s,x10 * s,x11 * s,x12 * s,x13 * s,x14 * s,x15 * s,x16 * s,x17 * s,x18 * s,x19 * s,x20 * s,x21 * s,x22 * s,x23 * s,x24 * s,x25 * s,x26 * s,x27 * s,x28 * s,x29 * s,x30 * s,x31 * s,x32 * s,x33 * s,x34 * s,x35 * s,x36 * s,x37 * s,x38 * s,x39 * s,x40 * s,x41 * s,x42 * s,x43 * s,x44 * s,x45 * s,x46 * s,x47 * s,x48 * s,x49 * s,x50 * s,x51 * s,x52 * s,x53 * s,x54 * s,x55 * s,x56 * s,x57 * s,x58 * s,x59 * s,x60 * s,x61 * s,x62 * s,x63 * s,x64 * s,x65 * s,x66 * s,x67 * s,x68 * s,x69 * s,x70 * s,x71 * s,x72 * s,x73 * s,x74 * s,x75 * s,x76 * s,x77 * s,x78 * s,x79 * s,x80 * s,x81 * s,x82 * s,x83 * s,x84 * s,x85 * s,x86 * s,x87 * s,x88 * s,x89 * s,x90 * s,x91 * s,x92 * s,x93 * s,x94 * s,x95 * s,x96 * s,x97 * s,x98 * s,x99 * s,x100 * s,x101 * s,x102 * s,x103 * s,x104 * s,x105 * s,x106 * s,x107 * s,x108 * s,x109 * s,x110 * s,x111 * s,x112 * s,x113 * s,x114 * s,x115 * s,x116 * s,x117 * s,x118 * s,x119 * s,x120 * s,x121 * s,x122 * s,x123 * s,x124 * s,x125 * s]
}
const Q_INV:felt252=0x590625348ee7b13ed5063a897278482929cf2104a53c8ebd06ba86c7dbd6164;
const W_Q_INV:felt252=0x740d950ce510909e495e78b2d19ba2174a2e745d9362434943ce965cde10b51;
const ZW_Q_INV:felt252=0x7a781d7f62adf2b9e0cb5118fa25748d9262489e7cb2bc46be86b286f285bbb;
const REJECT_NORM:felt252=0x100000000000000000000;
const ZETA_Q_INV:felt252=0x5280f2a59c8cbdc0b6fc301454e8e5d08ba7c1d6a0dca611dfa0aca711da4b8;
const ZERO_ACC7:Acc7=0;
#[inline(always)]
fn scaled_quotient(a:LazyCoeff,b:PackingZq,c:LazyCoeff)->felt252 {
let b:felt252=b.into();
a.value * b - c.value
}
#[inline(always)]
fn check_half9_zq(value:u128,a:[LazyCoeff; 9],c:[LazyCoeff; 9],q:NonZero<PackingQ>)->bool {
let [a0,a1,a2,a3,a4,a5,a6,a7,a8]=a;
let [c0,c1,c2,c3,c4,c5,c6,c7,c8]=c;
let x:Acc8=match downcast(value) {
Some(x)=>x,
None=>{ return false; },
};
let (x,d0)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a0,d0,c0)) {
return false;
}
let (x,d1)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a1,d1,c1)) {
return false;
}
let (x,d2)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a2,d2,c2)) {
return false;
}
let (x,d3)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a3,d3,c3)) {
return false;
}
let (x,d4)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a4,d4,c4)) {
return false;
}
let (x,d5)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a5,d5,c5)) {
return false;
}
let (x,d6)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a6,d6,c6)) {
return false;
}
let (x,d7)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a7,d7,c7)) {
return false;
}
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a8,x,c8)) {
return false;
}
true
}
#[inline(never)]
fn check_slots14_zq(
f:[felt252; 14],a:[[LazyCoeff; 18]; 14],c:[[LazyCoeff; 18]; 14],q:NonZero<PackingQ>,
)->bool {
let [f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13]=f;
let [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13]=a;
let [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13]=c;
check_slot_inl(f0,a0,c0,q)
&& check_slot_inl(f1,a1,c1,q)
&& check_slot_inl(f2,a2,c2,q)
&& check_slot_inl(f3,a3,c3,q)
&& check_slot_inl(f4,a4,c4,q)
&& check_slot_inl(f5,a5,c5,q)
&& check_slot_inl(f6,a6,c6,q)
&& check_slot_inl(f7,a7,c7,q)
&& check_slot_inl(f8,a8,c8,q)
&& check_slot_inl(f9,a9,c9,q)
&& check_slot_inl(f10,a10,c10,q)
&& check_slot_inl(f11,a11,c11,q)
&& check_slot_inl(f12,a12,c12,q)
&& check_slot_inl(f13,a13,c13,q)
}#[inline(always)]
fn check_slot_inl(felt:felt252,a:[LazyCoeff; 18],c:[LazyCoeff; 18],q:NonZero<PackingQ>)->bool {
let [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17]=a;
let [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17]=c;
let (high,low)=match u128s_from_felt252(felt) {
U128sFromFelt252Result::Wide(x)=>x,
U128sFromFelt252Result::Narrow(x)=>(0,x),
};
check_half9_zq(low,[a0,a1,a2,a3,a4,a5,a6,a7,a8],[c0,c1,c2,c3,c4,c5,c6,c7,c8],q)
&& check_half9_zq(high,[a9,a10,a11,a12,a13,a14,a15,a16,a17],[c9,c10,c11,c12,c13,c14,c15,c16,c17],q)
}
#[inline(never)]
fn check_last_slot_zq(felt:felt252,a:[LazyCoeff; 8],c:[LazyCoeff; 8],q:NonZero<PackingQ>)->bool {
let [a0,a1,a2,a3,a4,a5,a6,a7]=a;
let [c0,c1,c2,c3,c4,c5,c6,c7]=c;
let low=match u128s_from_felt252(felt) {
U128sFromFelt252Result::Narrow(x)=>x,
U128sFromFelt252Result::Wide(_)=>{ return false; },
};
let x:Acc7=match downcast(low) {
Some(x)=>x,
None=>{ return false; },
};
let (x,d0)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a0,d0,c0)) {
return false;
}
let (x,d1)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a1,d1,c1)) {
return false;
}
let (x,d2)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a2,d2,c2)) {
return false;
}
let (x,d3)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a3,d3,c3)) {
return false;
}
let (x,d4)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a4,d4,c4)) {
return false;
}
let (x,d5)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a5,d5,c5)) {
return false;
}
let (x,d6)=bounded_int_div_rem(x,q);
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a6,d6,c6)) {
return false;
}
if let U128sFromFelt252Result::Wide(_)=u128s_from_felt252(scaled_quotient(a7,x,c7)) {
return false;
}
true
}
#[inline(never)]
pub(crate) fn verify_tail(
s1_slots:@Box<[felt252; 29]>,t_slots:@Box<[felt252; 29]>,mut msg:Span<MsgCoeff>,
mut public_key:Span<felt252>,
)->bool {
core::internal::revoke_ap_tracking();
let q=packing_q_cell();
let mut norm_n:felt252=0;
let [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28]=(*s1_slots).unbox();
let x0=match unpack_chunk_ntt_n7([s0,s1,s2,s3,s4,s5,s6],ref norm_n,q,Q_INV) {
Some(v)=>v,
None=>{ return false; },
};
let x1=match unpack_chunk_ntt_n7([s7,s8,s9,s10,s11,s12,s13],ref norm_n,q,W_Q_INV) {
Some(v)=>v,
None=>{ return false; },
};
let x2=match unpack_chunk_ntt_n7([s14,s15,s16,s17,s18,s19,s20],ref norm_n,q,ZETA_Q_INV) {
Some(v)=>v,
None=>{ return false; },
};
let x3=match unpack_chunk_ntt_n7([s21,s22,s23,s24,s25,s26,s27],ref norm_n,q,ZW_Q_INV) {
Some(v)=>v,
None=>{ return false; },
};
let low=match u128s_from_felt252(s28) {
U128sFromFelt252Result::Narrow(x)=>x,
U128sFromFelt252Result::Wide(_)=>{ return false; },
};
let value:Acc7=match downcast(low) {
Some(v)=>v,
None=>{ return false; },
};
let (e0,e1,e2,e3,e4,e5,e6,e7)=digits8_np(value,ref norm_n,q);
let mut norm_d:felt252=0;
let [t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]=(*t_slots).unbox();
let y0=unpack_chunk_ntt_d7([t0,t1,t2,t3,t4,t5,t6],ref msg,ref norm_d,q,Q_INV);
let y1=unpack_chunk_ntt_d7([t7,t8,t9,t10,t11,t12,t13],ref msg,ref norm_d,q,W_Q_INV);
let y2=unpack_chunk_ntt_d7([t14,t15,t16,t17,t18,t19,t20],ref msg,ref norm_d,q,ZETA_Q_INV);
let y3=unpack_chunk_ntt_d7([t21,t22,t23,t24,t25,t26,t27],ref msg,ref norm_d,q,ZW_Q_INV);
let low=match u128s_from_felt252(t28) {
U128sFromFelt252Result::Narrow(x)=>x,
U128sFromFelt252Result::Wide(_)=>{
norm_d += REJECT_NORM;
0
},
};
let value:Acc7=match downcast(low) {
Some(v)=>v,
None=>{
norm_d += REJECT_NORM;
ZERO_ACC7
},
};
let [m0,m1,m2,m3,m4,m5,m6,m7]=(*msg.multi_pop_front::<8>().unwrap()).unbox();
let (te0,te1,te2,te3,te4,te5,te6,te7)=digits8_d(value,[m0,m1,m2,m3,m4,m5,m6,m7],ref norm_d,q);
let (sa,sb)=pqbench_ntt::falcon512_fast::ntt_falcon512_fast_lazy_slots(
[x0,x1,x2,x3],[e0,e1,e2,e3,e4,e5,e6,e7],0,Q_INV,ZW_Q_INV,
);
let (ta,tb)=pqbench_ntt::falcon512_fast::ntt_falcon512_fast_lazy_slots(
[y0,y1,y2,y3],[te0,te1,te2,te3,te4,te5,te6,te7],
crate::falcon::HINT_NTT_OFFSET,Q_INV,ZW_Q_INV,
);
let bound:Option<corelib_imports::bounded_int::BoundedInt<0,34034726>> = downcast(
norm_n + norm_d,
);
let mut ok=bound.is_some();
let [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27]=sa;
let [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27]=ta;
let [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28]=match public_key.multi_pop_front::<29>() {
Some(b)=>(*b).unbox(),
None=>{ return false; },
};
ok=ok & check_slots14_zq([p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13],[a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13],[c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13],q);
ok=ok & check_slots14_zq([p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27],[a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27],[c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27],q);
ok & check_last_slot_zq(p28,sb,tb,q)
}
