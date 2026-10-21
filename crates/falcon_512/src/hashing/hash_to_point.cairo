//! Hash-to-point for Falcon-512, three backends sharing one rejection rule
//! ([`push_candidate`]): the non-standard BLAKE2s counter-mode construction
//! ([`hash_to_point_512`]), the standard SHAKE-256 construction of the Falcon spec
//! ([`hash_to_point_shake_512`], interoperable with stock signers like falcon.py), and a
//! Poseidon squeeze over the native `hades_permutation` builtin
//! ([`hash_to_point_poseidon_512`], non-standard but native and inexpensive).
//!
//! ## BLAKE2s backend
//!
//! Maps `(message_hash, salt)` to 512 coefficients in `[0, Q)`:
//!
//! ```text
//! prefix   = salt_a[20 bytes LE] || salt_b[20 bytes LE] || message_hash[32 bytes LE]
//! digest_i = blake2s-256(prefix || u32_le(i))          for i = 0, 1, 2, ...
//! ```
//!
//! Each digest yields 16 little-endian u16 candidates, consumed in order; candidates
//! < 61445 (= 5Q, the largest multiple of Q below 2^16) are accepted as `candidate % Q`
//! (uniform in `[0, Q)`), until 512 coefficients are collected — the same rejection rule
//! as the SHAKE-256 construction in the Falcon spec.
//!
//! The salt is 40 bytes (the FIPS-206 salt length), carried as two felts of 20 bytes each.
//!
//! The XOF is BLAKE2s in counter mode (the Cairo-native `core::blake` builtin), not the
//! SHAKE-256 of FIPS 206: signatures are NOT FIPS-206-interoperable, and the off-chain
//! signer must hash with this exact construction (see `scripts/gen_falcon_fixture.py`).

use core::blake::{blake2s_compress, blake2s_finalize};
use core::poseidon::hades_permutation;
use corelib_imports::bounded_int::{
    BoundedInt, DivRemHelper, UnitInt, bounded_int_div_rem, downcast, upcast,
};
#[feature("bounded-int-utils")]
use core::internal::bounded_int::{ConstrainHelper,constrain};
use super::shake256::{Low,Row4,keccak_f1600_d,keccak_f1600_packed,keccak_next,pack,pack_exact};
use corelib_imports::bounded_int::{AddHelper,MulHelper,bounded_int};
type Q32=BoundedInt<0,0xffffffff>;
type T32=UnitInt<0x100000000>;
const T32_V:T32=0x100000000;
impl DivRemU128T32 of DivRemHelper<u128,T32> {
type DivT=BoundedInt<0,0xffffffffffffffffffffffff>;
type RemT=Q32;
}
impl DivRemQ96Two64 of DivRemHelper<BoundedInt<0,0xffffffffffffffffffffffff>,SqueezeTwo64> {
type DivT=Q32;
type RemT=Low;
}
type T96=UnitInt<0x1000000000000000000000000>;
impl DivRemU128T96 of DivRemHelper<u128,T96> {
type DivT=Q32;
type RemT=BoundedInt<0,0xffffffffffffffffffffffff>;
}
impl MulQ96T32 of MulHelper<BoundedInt<0,0xffffffffffffffffffffffff>,T32> {
type Result=BoundedInt<0,0xffffffffffffffffffffffff00000000>;
}
impl AddQ32Q96Hi of AddHelper<Q32,BoundedInt<0,0xffffffffffffffffffffffff00000000>> {
type Result=BoundedInt<0,0xffffffffffffffffffffffffffffffff>;
}
impl MulQ32T32 of MulHelper<Q32,T32> {
type Result=BoundedInt<0,0xffffffff00000000>;
}
impl AddQ32Hi of AddHelper<Q32,BoundedInt<0,0xffffffff00000000>> {
type Result=Low;
}

/// blake2s-256 initial state: the BLAKE2s IV with the standard parameter word
/// (digest_length = 32, key = 0, fanout = 1, depth = 1) XORed into h[0].
const BLAKE2S_256_INIT: [u32; 8] = [
    0x6B08E647, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

/// Rejection bound: the largest multiple of Q below 2^16 (5 * 12289).
const REJECT_BOUND: u32 = 61445;

/// Each salt felt must fit in 20 bytes.
const TWO_POW_160: u256 = 0x10000000000000000000000000000000000000000_u256;

/// Total bytes hashed per counter block: 40 (salt) + 32 (message hash) + 4 (counter).
const HASH_INPUT_BYTES: u32 = 76;

// Exact bounds for reading a felt's low 240 bits as little-endian 16-bit words.
// Each division peels one word; the final quotient after seven divisions is itself
// one 16-bit word for the low half and is discarded for the high half.
type Word16 = BoundedInt<0, 65535>;
type AcceptedWord = BoundedInt<0, 61444>;
type Base16 = UnitInt<65536>;
type Quot112 = BoundedInt<0, 5192296858534827628530496329220095>;
type Quot96 = BoundedInt<0, 79228162514264337593543950335>;
type Quot80 = BoundedInt<0, 1208925819614629174706175>;
type Quot64 = BoundedInt<0, 18446744073709551615>;
type Quot48 = BoundedInt<0, 281474976710655>;
type Quot32 = BoundedInt<0, 4294967295>;
type PoseidonQ = UnitInt<12289>;
type PoseidonZq = BoundedInt<0, 12288>;

const BASE16_NZ: NonZero<Base16> = 65536;
const POSEIDON_Q_NZ: NonZero<PoseidonQ> = 12289;

impl DivRemU128ByBase16 of DivRemHelper<u128, Base16> {
    type DivT = Quot112;
    type RemT = Word16;
}

impl DivRemQuot112ByBase16 of DivRemHelper<Quot112, Base16> {
    type DivT = Quot96;
    type RemT = Word16;
}

impl DivRemQuot96ByBase16 of DivRemHelper<Quot96, Base16> {
    type DivT = Quot80;
    type RemT = Word16;
}

impl DivRemQuot80ByBase16 of DivRemHelper<Quot80, Base16> {
    type DivT = Quot64;
    type RemT = Word16;
}

impl DivRemQuot64ByBase16 of DivRemHelper<Quot64, Base16> {
    type DivT = Quot48;
    type RemT = Word16;
}

impl DivRemQuot48ByBase16 of DivRemHelper<Quot48, Base16> {
    type DivT = Quot32;
    type RemT = Word16;
}

impl DivRemQuot32ByBase16 of DivRemHelper<Quot32, Base16> {
    type DivT = Word16;
    type RemT = Word16;
}

impl DivRemAcceptedWordByPoseidonQ of DivRemHelper<AcceptedWord, PoseidonQ> {
    type DivT = BoundedInt<0, 4>;
    type RemT = PoseidonZq;
}

/// Hash `(message_hash, salt)` to 512 coefficients in `[0, Q)`.
/// Returns `None` if either salt felt exceeds 20 bytes.
pub fn hash_to_point_512(
    message_hash: felt252, salt_a: felt252, salt_b: felt252,
) -> Option<Array<u16>> {
    let sa: u256 = salt_a.into();
    let sb: u256 = salt_b.into();
    if sa >= TWO_POW_160 || sb >= TWO_POW_160 {
        return None;
    }
    let (a0, a1, a2, a3, a4) = limbs_160(sa);
    let (b0, b1, b2, b3, b4) = limbs_160(sb);
    let mh: u256 = message_hash.into();
    let (m0, m1, m2, m3) = limbs_128(mh.low);
    let (m4, m5, m6, m7) = limbs_128(mh.high);

    // Bytes 0..63 (identical for every counter, so compressed once): the 40-byte salt
    // followed by the first 24 bytes of the message hash.
    let prefix_state = blake2s_compress(
        BoxTrait::new(BLAKE2S_256_INIT),
        64,
        BoxTrait::new([a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, m0, m1, m2, m3, m4, m5]),
    )
        .unbox();

    let sixteen_bits: NonZero<u32> = 0x10000_u32.try_into().unwrap();
    let q32: NonZero<u32> = 12289_u32.try_into().unwrap();
    let mut coeffs: Array<u16> = array![];
    let mut ctr: u32 = 0;
    while coeffs.len() != 512 {
        // Bytes 64..75: the last 8 bytes of the message hash and the LE counter.
        let digest = blake2s_finalize(
            BoxTrait::new(prefix_state),
            HASH_INPUT_BYTES,
            BoxTrait::new([m6, m7, ctr, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        )
            .unbox();
        let mut words = digest.span();
        while let Some(w) = words.pop_front() {
            // Two LE u16 candidates per digest word, low half first.
            let (hi, lo) = DivRem::div_rem(*w, sixteen_bits);
            push_candidate(lo, q32, ref coeffs);
            push_candidate(hi, q32, ref coeffs);
        }
        ctr += 1;
    }
    Some(coeffs)
}

/// Rejection-sample one 16-bit candidate: accept `candidate % Q` while below the
/// bound and 512 coefficients have not been collected yet.
#[inline(always)]
fn push_candidate(candidate: u32, q32: NonZero<u32>, ref coeffs: Array<u16>) {
    if coeffs.len() != 512 && candidate < REJECT_BOUND {
        let (_, r) = DivRem::div_rem(candidate, q32);
        coeffs.append(r.try_into().unwrap());
    }
}

/// ## SHAKE-256 backend
///
/// The standard Falcon (FIPS 206) construction: absorb `salt || message_hash` with
/// SHAKE-256, then consume the squeezed stream as big-endian 16-bit words, applying the
/// shared [`push_candidate`] rule (accept `word % Q` while `word < 5Q`) until 512
/// coefficients are collected. Unlike the BLAKE2s backend this is interoperable with any
/// standards-compliant Falcon signer (e.g. falcon.py). The message hash is absorbed as
/// its 32 little-endian bytes, the salt as its two 20-byte little-endian halves.
///
/// The sponge is driven directly on the Keccak lanes: the 72-byte input fits a single
/// rate block whose padded lanes are assembled straight from the salt and message-hash
/// limbs, and squeezing reads candidate words from the 17 rate lanes in place
/// ([`push_lane_words`]), permuting again only while more candidates are needed.

/// Hash `(message_hash, salt)` to 512 coefficients in `[0, Q)` with the standard
/// SHAKE-256 construction. Returns `None` if either salt felt exceeds 20 bytes.
pub fn hash_to_point_shake_512(
    message_hash: felt252, salt_a: felt252, salt_b: felt252,
) -> Option<Array<u16>> {
    let sa: u256 = salt_a.into();
    let sb: u256 = salt_b.into();
    if sa >= TWO_POW_160 || sb >= TWO_POW_160 {
        return None;
    }
    let mh: u256 = message_hash.into();

    // The absorbed block, assembled directly as little-endian lanes: bytes 0..40 hold
    // the salt, 40..72 the message hash, byte 72 the 0x1F SHAKE domain byte, and byte
    // 135 the pad10*1 terminator. The sponge state starts at zero, so this first
    // (and only) absorbed block IS the pre-permutation state.
    let two64: NonZero<u128> = 0x10000000000000000_u128.try_into().unwrap();
    let two32: NonZero<u128> = 0x100000000_u128.try_into().unwrap();
    let (a1, a0) = DivRem::div_rem(sa.low, two64); // salt_a bytes 0..8 and 8..16
    let (sbq, sb0) = DivRem::div_rem(sb.low, two32); // salt_b bytes 0..4 and 4..16
    let (sb12, l3) = DivRem::div_rem(sbq, two64); // salt_b bytes 4..12 -> lane 3
    let (m1, m0) = DivRem::div_rem(mh.low, two64);
    let (m3, m2) = DivRem::div_rem(mh.high, two64);
    // Lane 2: salt_a bytes 16..20 in the low half, salt_b bytes 0..4 in the high half.
    let l2: u128 = (sa.high.into() + sb0.into() * 0x100000000).try_into().unwrap();
    // Lane 4: salt_b bytes 12..16 in the low half, salt_b bytes 16..20 in the high half.
    let l4: u128 = (sb12.into() + sb.high.into() * 0x100000000).try_into().unwrap();

let mut state=keccak_f1600_packed(
        [
pack(a0,a1),pack(m0,m1),0,0x80000000000000000000000000000000,0,pack(l2,l3),
pack(m2,m3),0,0,0,pack(l4,0x1f),0,0,
        ],
    );

    let mut coeffs: Array<u16> = array![];
let k=squeeze_consts();
    loop {
push_block(@state,ref coeffs,k);
        if coeffs.len() == 512 {
            break;
        }
state=keccak_f1600_packed(state);
    }
    Some(coeffs)
}

#[derive(Copy,Drop)]
struct SqueezeConsts {
two64:NonZero<SqueezeTwo64>,
base16:NonZero<Base16>,
q:NonZero<PoseidonQ>,
even_bytes:u128,
two24:NonZero<Two24>,
two72:NonZero<Two72>,
}
#[inline(never)]
fn squeeze_init()->(Array<MsgCoeff>,felt252) {
(array![],1)
}
#[inline(never)]
fn squeeze_consts()->SqueezeConsts {
SqueezeConsts {
two64:0x10000000000000000,base16:BASE16_NZ,q:POSEIDON_Q_NZ,even_bytes:EVEN_BYTES_128,
two24:0x1000000,two72:0x1000000000000000000,
}
}
type SqueezeTwo64=UnitInt<0x10000000000000000>;
type SqueezeLane=BoundedInt<0,0xffffffffffffffff>;
impl DivRemSqueezeWord of DivRemHelper<u128,SqueezeTwo64> {
type DivT=SqueezeLane;
type RemT=SqueezeLane;
}
#[inline(always)]
fn split_lanes(w:u128,k:SqueezeConsts)->(u128,u128) {
let (high,low)=bounded_int_div_rem(w,k.two64);
(upcast(high),upcast(low))
}
type Swapped128=BoundedInt<0,0xffffffffffffffffffffffffffffffff>;
type Swapped112=BoundedInt<0,0xffffffffffffffffffffffffffff>;
type Swapped96=BoundedInt<0,0xffffffffffffffffffffffff>;
type Swapped80=BoundedInt<0,0xffffffffffffffffffff>;
type Swapped48=BoundedInt<0,0xffffffffffff>;
type Swapped32=BoundedInt<0,0xffffffff>;
impl DivRemSwapped128 of DivRemHelper<Swapped128,Base16> {
type DivT=Swapped112;
type RemT=Word16;
}
const EVEN_BYTES_128:u128=0x00ff00ff00ff00ff00ff00ff00ff00ff;
#[inline(always)]
fn swap_word(w:u128,k:SqueezeConsts)->Swapped128 {
let even:u128=w & k.even_bytes;
let even_f:felt252=even.into();
let w_f:felt252=w.into();
let swapped:u128=(even_f * 256 + (w_f - even_f) * INV_256).try_into().unwrap();
upcast(swapped)
}
#[inline(always)]
fn word_chunks(
w:Swapped128,k:SqueezeConsts,
)->(Word16,Word16,Word16,Word16,Word16,Word16,Word16,Word16) {
let (q,c0)=bounded_int_div_rem(w,k.base16);
let (q,c1)=bounded_int_div_rem(q,k.base16);
let (q,c2)=bounded_int_div_rem(q,k.base16);
let (q,c3)=bounded_int_div_rem(q,k.base16);
let (q,c4)=bounded_int_div_rem(q,k.base16);
let (q,c5)=bounded_int_div_rem(q,k.base16);
let (c7,c6)=bounded_int_div_rem(q,k.base16);
(c0,c1,c2,c3,c4,c5,c6,c7)
}
#[inline(always)]
fn low_lane_chunks(w:Swapped128,k:SqueezeConsts)->(Word16,Word16,Word16,Word16) {
let (q,c0)=bounded_int_div_rem(w,k.base16);
let (q,c1)=bounded_int_div_rem(q,k.base16);
let (q,c2)=bounded_int_div_rem(q,k.base16);
let (_,c3)=bounded_int_div_rem(q,k.base16);
(c0,c1,c2,c3)
}
#[inline(always)]
fn push_word8_uncapped(w:u128,ref coeffs:Array<u16>,k:SqueezeConsts) {
let (c0,c1,c2,c3,c4,c5,c6,c7)=word_chunks(swap_word(w,k),k);
push_shake_candidate_uncapped(c0,ref coeffs,k);
push_shake_candidate_uncapped(c1,ref coeffs,k);
push_shake_candidate_uncapped(c2,ref coeffs,k);
push_shake_candidate_uncapped(c3,ref coeffs,k);
push_shake_candidate_uncapped(c4,ref coeffs,k);
push_shake_candidate_uncapped(c5,ref coeffs,k);
push_shake_candidate_uncapped(c6,ref coeffs,k);
push_shake_candidate_uncapped(c7,ref coeffs,k);
}
#[inline(always)]
fn push_word8_capped(w:u128,ref coeffs:Array<u16>,k:SqueezeConsts) {
let (c0,c1,c2,c3,c4,c5,c6,c7)=word_chunks(swap_word(w,k),k);
push_shake_candidate(c0,ref coeffs,k);
push_shake_candidate(c1,ref coeffs,k);
push_shake_candidate(c2,ref coeffs,k);
push_shake_candidate(c3,ref coeffs,k);
push_shake_candidate(c4,ref coeffs,k);
push_shake_candidate(c5,ref coeffs,k);
push_shake_candidate(c6,ref coeffs,k);
push_shake_candidate(c7,ref coeffs,k);
}
#[inline(always)]
fn push_word8(w:u128,ref coeffs:Array<u16>,k:SqueezeConsts) {
if coeffs.len() <= 512 - 8 {
push_word8_uncapped(w,ref coeffs,k);
} else {
push_word8_capped(w,ref coeffs,k);
}
}
#[inline(always)]
fn push4_uncapped(c0:Word16,c1:Word16,c2:Word16,c3:Word16,ref coeffs:Array<u16>,k:SqueezeConsts) {
push_shake_candidate_uncapped(c0,ref coeffs,k);
push_shake_candidate_uncapped(c1,ref coeffs,k);
push_shake_candidate_uncapped(c2,ref coeffs,k);
push_shake_candidate_uncapped(c3,ref coeffs,k);
}
#[inline(always)]
fn push4(c0:Word16,c1:Word16,c2:Word16,c3:Word16,ref coeffs:Array<u16>,k:SqueezeConsts) {
if coeffs.len() <= 512 - 4 {
push4_uncapped(c0,c1,c2,c3,ref coeffs,k);
} else {
push_shake_candidate(c0,ref coeffs,k);
push_shake_candidate(c1,ref coeffs,k);
push_shake_candidate(c2,ref coeffs,k);
push_shake_candidate(c3,ref coeffs,k);
}
}
#[inline(always)]
fn push_block(state:@[u128; 13],ref coeffs:Array<u16>,k:SqueezeConsts) {
let [u0,u1,u2,u3,_,v0,v1,v2,_,_,g01,g23,_] = *state;
let (g0,g1,g2,g3,g4,g5,g6,g7)=word_chunks(swap_word(g01,k),k);
if coeffs.len() <= 512 - 68 {
push_word8_uncapped(u0,ref coeffs,k);
push_word8_uncapped(v0,ref coeffs,k);
push4_uncapped(g0,g1,g2,g3,ref coeffs,k);
push_word8_uncapped(u1,ref coeffs,k);
push_word8_uncapped(v1,ref coeffs,k);
push4_uncapped(g4,g5,g6,g7,ref coeffs,k);
push_word8_uncapped(u2,ref coeffs,k);
push_word8_uncapped(v2,ref coeffs,k);
let (h0,h1,h2,h3)=low_lane_chunks(swap_word(g23,k),k);
push4_uncapped(h0,h1,h2,h3,ref coeffs,k);
push_word8_uncapped(u3,ref coeffs,k);
} else {
push_word8(u0,ref coeffs,k);
push_word8(v0,ref coeffs,k);
push4(g0,g1,g2,g3,ref coeffs,k);
push_word8(u1,ref coeffs,k);
push_word8(v1,ref coeffs,k);
push4(g4,g5,g6,g7,ref coeffs,k);
push_word8(u2,ref coeffs,k);
push_word8(v2,ref coeffs,k);
let (h0,h1,h2,h3)=low_lane_chunks(swap_word(g23,k),k);
push4(h0,h1,h2,h3,ref coeffs,k);
push_word8(u3,ref coeffs,k);
}
}
impl DivRemWord16ByPoseidonQ of DivRemHelper<Word16,PoseidonQ> {
type DivT=BoundedInt<0,5>;
type RemT=PoseidonZq;
}
#[inline(always)]
fn push_shake_candidate(candidate:Word16,ref coeffs:Array<u16>,k:SqueezeConsts) {
if coeffs.len() == 512 {
return;
}
let (k,r)=bounded_int_div_rem(candidate,k.q);
let k:felt252=k.into();
if k != 5 {
coeffs.append(upcast(r));
}
}
const INV_256:felt252=0x7f8000000000010ef0000000000000000000000000000000000000000000001;
const EVEN_BYTES:u128=0x00ff00ff00ff00ff;
/// Read one squeezed rate lane (< 2^64) as four big-endian 16-bit candidate words. The
/// lane's bytes are little-endian, so each 16-bit chunk holds its stream word
/// byte-swapped: chunk = b0 + 256*b1 for the stream word 256*b0 + b1.
#[inline(always)]
fn push_lane_words(lane:u128,ref coeffs:Array<u16>,k:SqueezeConsts) {
let even:u128=lane & k.even_bytes;
let even_f:felt252=even.into();
let lane_f:felt252=lane.into();
let swapped_f:felt252=even_f * 256 + (lane_f - even_f) * INV_256;
let swapped:u64=swapped_f.try_into().unwrap();
let swapped:Quot64=upcast(swapped);
let (q1,w0)=bounded_int_div_rem(swapped,k.base16);
let (q2,w1)=bounded_int_div_rem(q1,k.base16);
let (w3,w2)=bounded_int_div_rem(q2,k.base16);
push_shake_candidate(w0,ref coeffs,k);
push_shake_candidate(w1,ref coeffs,k);
push_shake_candidate(w2,ref coeffs,k);
push_shake_candidate(w3,ref coeffs,k);
}

#[inline(always)]
fn push_shake_candidate_uncapped(candidate:Word16,ref coeffs:Array<u16>,k:SqueezeConsts) {
let (k,r)=bounded_int_div_rem(candidate,k.q);
let k:felt252=k.into();
if k != 5 {
coeffs.append(upcast(r));
}
}
/// ## Poseidon backend
///
/// Absorb `(salt_a, salt_b, message_hash)` as three field elements with the native Poseidon
/// permutation (`hades_permutation`, a Starknet builtin), then squeeze — take the two rate
/// elements `(s0, s1)` of the state, read 15 little-endian 16-bit words from the low 240
/// bits of each (uniform, since the field prime exceeds `2^251`), apply the shared
/// [`push_candidate`] rule, and permute the state again for the next block until 512
/// coefficients are collected.
///
/// Non-standard (Poseidon is not in the Falcon spec), so the off-chain signer must match
/// this construction (see `scripts/gen_falcon_fixture.py --variant poseidon`). Every step
/// is a native field operation, so the hash-to-point is inexpensive: on-chain verify cost
/// is close to the BLAKE2s backend and far below the pure-Cairo SHAKE-256 (the shared
/// NTT/hint core dominates either way).

/// Hash `(message_hash, salt)` to 512 coefficients in `[0, Q)` with a Poseidon squeeze.
/// Returns `None` if either salt felt exceeds 20 bytes.
pub fn hash_to_point_poseidon_512(
    message_hash: felt252, salt_a: felt252, salt_b: felt252,
) -> Option<Array<u16>> {
    let sa: u256 = salt_a.into();
    let sb: u256 = salt_b.into();
    if sa >= TWO_POW_160 || sb >= TWO_POW_160 {
        return None;
    }
    // Absorb the three inputs, then squeeze the rate elements two felts at a time.
    let (mut s0, mut s1, mut s2) = hades_permutation(salt_a, salt_b, message_hash);
    let mut coeffs: Array<u16> = array![];
    while coeffs.len() != 512 {
        push_felt_words(s0, ref coeffs);
        push_felt_words(s1, ref coeffs);
        if coeffs.len() == 512 {
            break;
        }
        let (n0, n1, n2) = hades_permutation(s0, s1, s2);
        s0 = n0;
        s1 = n1;
        s2 = n2;
    }
    Some(coeffs)
}

/// Read the low 240 bits of `felt` as 15 little-endian 16-bit candidate words — 8 from
/// the low 128-bit half and 7 from the high half.
fn push_felt_words(felt: felt252, ref coeffs: Array<u16>) {
    let v: u256 = felt.into();
    push_u128_words8(v.low, ref coeffs);
    push_u128_words7(v.high, ref coeffs);
}

/// Feed all eight 16-bit words of a u128, low first, as rejection-sampled candidates.
#[inline(always)]
fn push_u128_words8(value: u128, ref coeffs: Array<u16>) {
    let (q1, w0) = bounded_int_div_rem(value, BASE16_NZ);
    let (q2, w1) = bounded_int_div_rem(q1, BASE16_NZ);
    let (q3, w2) = bounded_int_div_rem(q2, BASE16_NZ);
    let (q4, w3) = bounded_int_div_rem(q3, BASE16_NZ);
    let (q5, w4) = bounded_int_div_rem(q4, BASE16_NZ);
    let (q6, w5) = bounded_int_div_rem(q5, BASE16_NZ);
    let (w7, w6) = bounded_int_div_rem(q6, BASE16_NZ);
    push_poseidon_candidate(w0, ref coeffs);
    push_poseidon_candidate(w1, ref coeffs);
    push_poseidon_candidate(w2, ref coeffs);
    push_poseidon_candidate(w3, ref coeffs);
    push_poseidon_candidate(w4, ref coeffs);
    push_poseidon_candidate(w5, ref coeffs);
    push_poseidon_candidate(w6, ref coeffs);
    push_poseidon_candidate(w7, ref coeffs);
}

/// Feed the low seven 16-bit words of a u128 and discard its remaining high 16 bits.
#[inline(always)]
fn push_u128_words7(value: u128, ref coeffs: Array<u16>) {
    let (q1, w0) = bounded_int_div_rem(value, BASE16_NZ);
    let (q2, w1) = bounded_int_div_rem(q1, BASE16_NZ);
    let (q3, w2) = bounded_int_div_rem(q2, BASE16_NZ);
    let (q4, w3) = bounded_int_div_rem(q3, BASE16_NZ);
    let (q5, w4) = bounded_int_div_rem(q4, BASE16_NZ);
    let (q6, w5) = bounded_int_div_rem(q5, BASE16_NZ);
    let (_, w6) = bounded_int_div_rem(q6, BASE16_NZ);
    push_poseidon_candidate(w0, ref coeffs);
    push_poseidon_candidate(w1, ref coeffs);
    push_poseidon_candidate(w2, ref coeffs);
    push_poseidon_candidate(w3, ref coeffs);
    push_poseidon_candidate(w4, ref coeffs);
    push_poseidon_candidate(w5, ref coeffs);
    push_poseidon_candidate(w6, ref coeffs);
}

/// Apply the unchanged Falcon rejection rule to one exact 16-bit Poseidon word.
#[inline(always)]
fn push_poseidon_candidate(candidate: Word16, ref coeffs: Array<u16>) {
    if coeffs.len() == 512 {
        return;
    }
    match downcast::<Word16, AcceptedWord>(candidate) {
        Some(accepted) => {
            let (_, r) = bounded_int_div_rem(accepted, POSEIDON_Q_NZ);
            coeffs.append(upcast(r));
        },
        None => {},
    }
}

/// Little-endian u32 limbs of a u128.
fn limbs_128(x: u128) -> (u32, u32, u32, u32) {
    let two_pow_32: NonZero<u128> = 0x100000000_u128.try_into().unwrap();
    let (rest, l0) = DivRem::div_rem(x, two_pow_32);
    let (rest, l1) = DivRem::div_rem(rest, two_pow_32);
    let (l3, l2) = DivRem::div_rem(rest, two_pow_32);
    (l0.try_into().unwrap(), l1.try_into().unwrap(), l2.try_into().unwrap(), l3.try_into().unwrap())
}

/// Little-endian u32 limbs of a 160-bit value (caller checks the range).
fn limbs_160(x: u256) -> (u32, u32, u32, u32, u32) {
    let (l0, l1, l2, l3) = limbs_128(x.low);
    (l0, l1, l2, l3, x.high.try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::{TWO_POW_160, hash_to_point_512};

    const MSG: felt252 = 'BENCH_MSG';

    // Known-answer vectors generated with the reference Python construction
    // (hashlib.blake2s counter mode; see scripts/gen_falcon_fixture.py).
    #[test]
    fn test_hash_to_point_kat() {
        let coeffs = hash_to_point_512(MSG, 1, 2).unwrap();
        assert_eq!(coeffs.len(), 512);
        let first8: [u16; 8] = [9961, 3944, 2517, 2545, 1832, 3277, 10883, 3861];
        let last8: [u16; 8] = [5236, 2206, 424, 1825, 8022, 8816, 4999, 9640];
        let mid4: [u16; 4] = [9941, 5062, 7268, 7838];
        let mut i: u32 = 0;
        for expected in first8.span() {
            assert_eq!(*coeffs.at(i), *expected);
            i += 1;
        }
        let mut j: u32 = 504;
        for expected in last8.span() {
            assert_eq!(*coeffs.at(j), *expected);
            j += 1;
        }
        let mut k: u32 = 255;
        for expected in mid4.span() {
            assert_eq!(*coeffs.at(k), *expected);
            k += 1;
        }
    }

    #[test]
    fn test_hash_to_point_domain_separation() {
        // Different message, salt halves, or salt order all change the point.
        let base = hash_to_point_512(MSG, 1, 2).unwrap();
        let other_msg = hash_to_point_512('OTHER_MSG', 1, 2).unwrap();
        let other_salt = hash_to_point_512(MSG, 2, 1).unwrap();
        assert_ne!(base.span(), other_msg.span());
        assert_ne!(base.span(), other_salt.span());
    }

    #[test]
    fn test_hash_to_point_rejects_oversized_salt() {
        let too_big: felt252 = TWO_POW_160.try_into().unwrap();
        assert!(hash_to_point_512(MSG, too_big, 0).is_none());
        assert!(hash_to_point_512(MSG, 0, too_big).is_none());
        // 2^160 - 1 is the largest valid salt half.
        assert!(hash_to_point_512(MSG, too_big - 1, too_big - 1).is_some());
    }
}
impl ConstrainWord16FiveQ of ConstrainHelper<Word16,61445> {
type LowT=BoundedInt<0,61444>;
type HighT=BoundedInt<61445,65535>;
}
#[inline(never)]
fn raw_tail1(c0:Word16,ref coeffs:Array<MsgCoeff>) {
let mut i:u32=coeffs.len();
while i == 0 {
i += 1;
}
let l0=match constrain::<Word16,61445>(c0) {
Ok(l)=>l,
Err(_)=>{ return; },
};
coeffs.append(upcast(l0));
}
#[inline(always)]
fn push_block_fast(state:@[u128; 10],ref coeffs:Array<MsgCoeff>,k:SqueezeConsts) {
let [u0,u1,u2,u3,v0,v1,v2,_,g01,g23] = *state;
let kd=Kd { b16:k.base16,b24:k.two24 };
let (s0,s1,s2,s3,s4,s5,s6)=(
swap_s(u0,k),swap_s(v0,k),swap_s(u1,k),swap_s(v1,k),swap_s(u2,k),swap_s(v2,k),
swap_s(u3,k),
);
let w01=swap_s(g01,k);
let w23=swap_s(g23,k);
Rd::run((s0,s1),kd,ref coeffs);
let (hi9,lo4)=bounded_int_div_rem(w01,k.two72);
Rd::run((Lo { v:upcast(lo4) },(s2,s3)),kd,ref coeffs);
Rd::run((Lo { v:bounded_int::mul(hi9,C256) },(s4,s5)),kd,ref coeffs);
let (_,lo14)=bounded_int_div_rem(w23,k.two72);
Rd::run((Lo { v:upcast(lo14) },s6),kd,ref coeffs);
}
type Sw144=BoundedInt<0,0xffffffffffffffffffffffffffffffff0000>;
type Two24=UnitInt<0x1000000>;
type Two72=UnitInt<0x1000000000000000000>;
type R24=BoundedInt<0,0xffffff>;
type Q120=BoundedInt<0,0xffffffffffffffffffffffffffffff>;
type Q104=BoundedInt<0,0xffffffffffffffffffffffffff>;
type Q88=BoundedInt<0,0xffffffffffffffffffffff>;
type Q72=BoundedInt<0,0xffffffffffffffffff>;
type Q56=BoundedInt<0,0xffffffffffffff>;
type Q40=BoundedInt<0,0xffffffffff>;
pub(crate) type MsgCoeff=BoundedInt<0,192549938479>;
type HeadOk=BoundedInt<0,15729919>;
const C65535:UnitInt<65535> = 65535;
const C12241:UnitInt<12241> = 12241;
impl MulEven65535 of MulHelper<u128,UnitInt<65535>> {
type Result=BoundedInt<0,0xfffeffffffffffffffffffffffffffff0001>;
}
impl AddEvenW of AddHelper<BoundedInt<0,0xfffeffffffffffffffffffffffffffff0001>,u128> {
type Result=Sw144;
}
impl DivRemSw144Two24 of DivRemHelper<Sw144,Two24> {
type DivT=Q120;
type RemT=R24;
}
impl DivRemSw144Two72 of DivRemHelper<Sw144,Two72> {
type DivT=Q72;
type RemT=Q72;
}
type LoT=BoundedInt<0,0xffffffffffffffffff00>;
const C256:UnitInt<256> = 256;
impl MulQ72By256 of MulHelper<Q72,UnitInt<256>> {
type Result=LoT;
}
impl DivRemLoTwo24 of DivRemHelper<LoT,Two24> {
type DivT=Q56;
type RemT=R24;
}
impl DivRemQ120 of DivRemHelper<Q120,Base16> {
type DivT=Q104;
type RemT=Word16;
}
impl DivRemQ104 of DivRemHelper<Q104,Base16> {
type DivT=Q88;
type RemT=Word16;
}
impl DivRemQ88 of DivRemHelper<Q88,Base16> {
type DivT=Q72;
type RemT=Word16;
}
impl DivRemQ72 of DivRemHelper<Q72,Base16> {
type DivT=Q56;
type RemT=Word16;
}
impl DivRemQ56 of DivRemHelper<Q56,Base16> {
type DivT=Q40;
type RemT=Word16;
}
impl DivRemQ40 of DivRemHelper<Q40,Base16> {
type DivT=R24;
type RemT=Word16;
}
impl ConstrainR24FiveQ of ConstrainHelper<R24,61445> {
type LowT=BoundedInt<0,61444>;
type HighT=BoundedInt<61445,0xffffff>;
}
impl ConstrainR24Head of ConstrainHelper<R24,15729920> {
type LowT=HeadOk;
type HighT=BoundedInt<15729920,0xffffff>;
}
impl MulHeadInv of MulHelper<HeadOk,UnitInt<12241>> {
type Result=MsgCoeff;
}
#[derive(Copy,Drop)]
struct Lo {
v:LoT,
}
#[derive(Copy,Drop)]
struct Kd {
b16:NonZero<Base16>,
b24:NonZero<Two24>,
}
#[inline(always)]
fn swap_s(w:u128,k:SqueezeConsts)->Sw144 {
let even:u128=w & k.even_bytes;
bounded_int::add(bounded_int::mul(even,C65535),w)
}
#[inline(never)]
fn raw_tail24(c0:R24,ref coeffs:Array<MsgCoeff>) {
let mut i:u32=coeffs.len();
while i == 0 {
i += 1;
}
let l0=match constrain::<R24,61445>(c0) {
Ok(l)=>l,
Err(_)=>{ return; },
};
coeffs.append(upcast(l0));
}
trait Rd<T> {
fn run(q:T,k:Kd,ref c:Array<MsgCoeff>);
fn tail(q:T,k:Kd,ref c:Array<MsgCoeff>);
}
#[inline(never)]
fn rdt<T,+Rd<T>,+Drop<T>>(q:T,k:Kd,ref c:Array<MsgCoeff>) {
Rd::run(q,k,ref c);
}
impl RdW of Rd<Word16> {
#[inline(always)]
fn run(q:Word16,k:Kd,ref c:Array<MsgCoeff>) {
if let Ok(l)=constrain::<Word16,61445>(q) {
c.append(upcast(l));
}
}
#[inline(always)]
fn tail(q:Word16,k:Kd,ref c:Array<MsgCoeff>) {
raw_tail1(q,ref c);
}
}
impl RdW24 of Rd<R24> {
#[inline(always)]
fn run(q:R24,k:Kd,ref c:Array<MsgCoeff>) {
if let Ok(l)=constrain::<R24,61445>(q) {
c.append(upcast(l));
}
}
#[inline(always)]
fn tail(q:R24,k:Kd,ref c:Array<MsgCoeff>) {
raw_tail24(q,ref c);
}
}
impl RdQ<
T,impl H:DivRemHelper<T,Base16>,+Rd<H::DivT>,+Drop<H::DivT>,+Drop<T>,
> of Rd<T> {
#[inline(always)]
fn run(q:T,k:Kd,ref c:Array<MsgCoeff>) {
let (q,w)=bounded_int_div_rem(q,k.b16);
match constrain::<Word16,61445>(upcast(w)) {
Ok(l)=>{
c.append(upcast(l));
Rd::run(q,k,ref c);
},
Err(_)=>Rd::tail(q,k,ref c),
}
}
#[inline(always)]
fn tail(q:T,k:Kd,ref c:Array<MsgCoeff>) {
rdt(q,k,ref c);
}
}
impl RdPW<N,+Rd<N>,+Drop<N>> of Rd<(Word16,N)> {
#[inline(always)]
fn run(q:(Word16,N),k:Kd,ref c:Array<MsgCoeff>) {
let (w,n)=q;
match constrain::<Word16,61445>(w) {
Ok(l)=>{
c.append(upcast(l));
Rd::run(n,k,ref c);
},
Err(_)=>Rd::tail(n,k,ref c),
}
}
#[inline(always)]
fn tail(q:(Word16,N),k:Kd,ref c:Array<MsgCoeff>) {
rdt(q,k,ref c);
}
}
impl RdPW24<N,+Rd<N>,+Drop<N>> of Rd<(R24,N)> {
#[inline(always)]
fn run(q:(R24,N),k:Kd,ref c:Array<MsgCoeff>) {
let (w,n)=q;
match constrain::<R24,61445>(w) {
Ok(l)=>{
c.append(upcast(l));
Rd::run(n,k,ref c);
},
Err(_)=>Rd::tail(n,k,ref c),
}
}
#[inline(always)]
fn tail(q:(R24,N),k:Kd,ref c:Array<MsgCoeff>) {
rdt(q,k,ref c);
}
}
impl RdP<
T,N,impl H:DivRemHelper<T,Base16>,+Rd<(H::DivT,N)>,+Drop<H::DivT>,+Drop<T>,+Drop<N>,
> of Rd<(T,N)> {
#[inline(always)]
fn run(q:(T,N),k:Kd,ref c:Array<MsgCoeff>) {
let (q,n)=q;
let (q,w)=bounded_int_div_rem(q,k.b16);
match constrain::<Word16,61445>(upcast(w)) {
Ok(l)=>{
c.append(upcast(l));
Rd::run((q,n),k,ref c);
},
Err(_)=>Rd::tail((q,n),k,ref c),
}
}
#[inline(always)]
fn tail(q:(T,N),k:Kd,ref c:Array<MsgCoeff>) {
rdt(q,k,ref c);
}
}
impl RdS of Rd<Sw144> {
#[inline(always)]
fn run(q:Sw144,k:Kd,ref c:Array<MsgCoeff>) {
let (q,h)=bounded_int_div_rem(q,k.b24);
match constrain::<R24,15729920>(h) {
Ok(l)=>{
c.append(bounded_int::mul(l,C12241));
Rd::run(q,k,ref c);
},
Err(_)=>Rd::tail(q,k,ref c),
}
}
#[inline(always)]
fn tail(q:Sw144,k:Kd,ref c:Array<MsgCoeff>) {
rdt(q,k,ref c);
}
}
impl RdSP<N,+Rd<N>,+Drop<N>> of Rd<(Sw144,N)> {
#[inline(always)]
fn run(q:(Sw144,N),k:Kd,ref c:Array<MsgCoeff>) {
let (q,n)=q;
let (q,h)=bounded_int_div_rem(q,k.b24);
match constrain::<R24,15729920>(h) {
Ok(l)=>{
c.append(bounded_int::mul(l,C12241));
Rd::run((q,n),k,ref c);
},
Err(_)=>Rd::tail((q,n),k,ref c),
}
}
#[inline(always)]
fn tail(q:(Sw144,N),k:Kd,ref c:Array<MsgCoeff>) {
rdt(q,k,ref c);
}
}
trait Cp<T> {
fn cap(q:T,k:Kd,ref c:Array<MsgCoeff>);
}
impl CpW24 of Cp<R24> {
#[inline(always)]
fn cap(q:R24,k:Kd,ref c:Array<MsgCoeff>) {
RdW24::run(q,k,ref c);
}
}
impl CpQ<
T,impl H:DivRemHelper<T,Base16>,+Cp<H::DivT>,+Drop<H::DivT>,+Drop<T>,
> of Cp<T> {
#[inline(always)]
fn cap(q:T,k:Kd,ref c:Array<MsgCoeff>) {
let (q,w)=bounded_int_div_rem(q,k.b16);
RdW::run(upcast(w),k,ref c);
if c.len() != 512 {
Cp::cap(q,k,ref c);
}
}
}
impl CpS of Cp<Sw144> {
#[inline(always)]
fn cap(q:Sw144,k:Kd,ref c:Array<MsgCoeff>) {
let (q,h)=bounded_int_div_rem(q,k.b24);
if let Ok(l)=constrain::<R24,15729920>(h) {
c.append(bounded_int::mul(l,C12241));
}
if c.len() != 512 {
Cp::cap(q,k,ref c);
}
}
}
impl RdL of Rd<Lo> {
#[inline(always)]
fn run(q:Lo,k:Kd,ref c:Array<MsgCoeff>) {
let (q,h)=bounded_int_div_rem(q.v,k.b24);
match constrain::<R24,15729920>(h) {
Ok(l)=>{
c.append(bounded_int::mul(l,C12241));
Rd::run(q,k,ref c);
},
Err(_)=>Rd::tail(q,k,ref c),
}
}
#[inline(always)]
fn tail(q:Lo,k:Kd,ref c:Array<MsgCoeff>) {
rdt(q,k,ref c);
}
}
impl RdLP<N,+Rd<N>,+Drop<N>> of Rd<(Lo,N)> {
#[inline(always)]
fn run(q:(Lo,N),k:Kd,ref c:Array<MsgCoeff>) {
let (lo,n)=q;
let (q,h)=bounded_int_div_rem(lo.v,k.b24);
match constrain::<R24,15729920>(h) {
Ok(l)=>{
c.append(bounded_int::mul(l,C12241));
Rd::run((q,n),k,ref c);
},
Err(_)=>Rd::tail((q,n),k,ref c),
}
}
#[inline(always)]
fn tail(q:(Lo,N),k:Kd,ref c:Array<MsgCoeff>) {
rdt(q,k,ref c);
}
}
#[inline(always)]
pub(crate) fn hash_to_point_shake_512_raw(
message_hash:felt252,salt_a:felt252,salt_b:felt252,
)->Option<Array<MsgCoeff>> {
hash_to_point_shake_512_raw_tail(message_hash,salt_a,salt_b,SYSCALL_TAIL_MISSING)
}
#[inline(always)]
fn hash_to_point_shake_512_raw_tail(
message_hash:felt252,salt_a:felt252,salt_b:felt252,tail:u32,
)->Option<Array<MsgCoeff>> {
let sa:u256=salt_a.into();
let sb:u256=salt_b.into();
let sah:Q32=match downcast(sa.high) { Some(v)=>v,None=>{ return None; } };
let sbh:Q32=match downcast(sb.high) { Some(v)=>v,None=>{ return None; } };
let mh:u256=message_hash.into();
let t64:NonZero<SqueezeTwo64> = 0x10000000000000000;
let t96:NonZero<T96> = 0x1000000000000000000000000;
let (sb12,sb96)=bounded_int_div_rem(sb.low,t96);
let wl23:u128=upcast(bounded_int::add(sah,bounded_int::mul(sb96,T32_V)));
let l4:Low=bounded_int::add(sb12,bounded_int::mul(sbh,T32_V));
let (state,r4)=keccak_f1600_d(
[
sa.low,mh.low,0,0x80000000000000000000000000000000,0,
wl23,mh.high,0,0,0,pack_exact(l4,0x1f),0,
],
0,
(sa.low ^ mh.low ^ 0x80000000000000000000000000000000,wl23 ^ mh.high,upcast(upcast::<Low,u64>(l4) ^ 0x1f)),
);
let block:AbsorbedBlock=([sa.low,mh.low,mh.high,wl23],l4);
Some(squeeze_raw(state,r4,block,tail))
}
const SYSCALL_TAIL_MISSING:u32=15;
type AbsorbedBlock=([u128; 4],Low);
#[inline(always)]
fn absorbed_lanes(block:AbsorbedBlock)->[Low; 9] {
let ([wa,wm0,wm1,wl23],l4)=block;
let t64:NonZero<SqueezeTwo64> = 0x10000000000000000;
let (a1,a0)=bounded_int_div_rem(wa,t64);
let (m1,m0)=bounded_int_div_rem(wm0,t64);
let (m3,m2)=bounded_int_div_rem(wm1,t64);
let (l3,l2)=bounded_int_div_rem(wl23,t64);
[a0,a1,l2,l3,l4,m0,m1,m2,m3]
}
#[inline(never)]
fn shake_head_lanes(block:[Low; 9],zero_blocks:u32)->u256 {
let [a0,a1,l2,l3,l4,m0,m1,m2,m3]=block;
let input:[u64; 153]=[
upcast(a0),upcast(a1),upcast(l2),upcast(l3),upcast(l4),upcast(m0),upcast(m1),upcast(m2),upcast(m3),0x1f,
0,0,0,0,0,0,0x8000000000000000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
];
starknet::SyscallResultTrait::unwrap_syscall(
starknet::syscalls::keccak_syscall(input.span().slice(0,(zero_blocks + 1) * 17)),
)
}
#[inline(never)]
fn shake_head_lanes8(block:[Low; 9])->u256 {
let [a0,a1,l2,l3,l4,m0,m1,m2,m3]=block;
let input:[u64; 153]=[
upcast(a0),upcast(a1),upcast(l2),upcast(l3),upcast(l4),upcast(m0),upcast(m1),upcast(m2),upcast(m3),0x1f,
0,0,0,0,0,0,0x8000000000000000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
];
starknet::SyscallResultTrait::unwrap_syscall(starknet::syscalls::keccak_syscall(input.span()))
}
#[inline(always)]
pub(crate) fn squeeze_raw(
mut state:[u128; 10],mut r4:Row4,block:AbsorbedBlock,tail:u32,
)->Array<MsgCoeff> {
let (mut coeffs,mut blocks)=squeeze_init();
let k=squeeze_consts();
let limit=512 - tail;
let SqueezeConsts { base16,even_bytes,two24,two72,.. }=k;
loop {
push_block_fast(@state,ref coeffs,SqueezeConsts { two64:0x10000000000000000,base16,q:POSEIDON_Q_NZ,even_bytes,two24,two72 });
if coeffs.len() >= limit {
break;
}
blocks += 1;
let (s,r)=keccak_next((state,r4));
state=s;
r4=r;
}
if coeffs.len() >= 512 {
return coeffs;
}
squeeze_raw_last(state,r4,block,blocks,coeffs,k)
}
#[inline(always)]
fn squeeze_raw_last(
state:[u128; 10],r4:Row4,block:AbsorbedBlock,blocks:felt252,mut coeffs:Array<MsgCoeff>,k:SqueezeConsts,
)->Array<MsgCoeff> {
let [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]=state;
let mut state:[u128; 10]=[
upcast(a0),upcast(a1),upcast(a2),upcast(a3),upcast(a4),upcast(a5),upcast(a6),upcast(a7),
upcast(a8),upcast(a9),
];
let mut r4=r4;
let mut all=true;
if blocks == 8 {
let head=shake_head_lanes8(absorbed_lanes(block));
let kd=Kd { b16:k.base16,b24:k.two24 };
let w0=swap_s(head.low,k);
if coeffs.len() <= 512 - 8 {
Rd::run(w0,kd,ref coeffs);
} else {
Cp::cap(w0,kd,ref coeffs);
}
if coeffs.len() == 512 {
return coeffs;
}
Cp::cap(swap_s(head.high,k),kd,ref coeffs);
if coeffs.len() == 512 {
return coeffs;
}
all=false;
}
while coeffs.len() < 512 {
let (s,r)=keccak_next((state,r4));
state=s;
r4=r;
push_block_lanes_raw(@state,ref coeffs,k,all);
all=true;
}
coeffs
}
#[inline(never)]
fn push_block_lanes_raw(state:@[u128; 10],ref coeffs:Array<MsgCoeff>,k:SqueezeConsts,head:bool) {
let [u0,u1,u2,u3,v0,v1,v2,_,g01,g23] = *state;
let mut lanes:Array<u128> = array![];
if head {
let (l1,l0)=split_lanes(u0,k);
let (l3,l2)=split_lanes(v0,k);
lanes.append(l0);
lanes.append(l1);
lanes.append(l2);
lanes.append(l3);
}
let (l9,l4)=split_lanes(g01,k);
let (l6,l5)=split_lanes(u1,k);
let (l8,l7)=split_lanes(v1,k);
let (l11,l10)=split_lanes(u2,k);
let (l13,l12)=split_lanes(v2,k);
let (_,l14)=split_lanes(g23,k);
let (l16,l15)=split_lanes(u3,k);
lanes.append_span(array![l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16].span());
let mut lanes=lanes.span();
let kd=Kd { b16:k.base16,b24:k.two24 };
while let Some(lane)=lanes.pop_front() {
if coeffs.len() >= 512 {
break;
}
let (_,lo)=bounded_int_div_rem(swap_s(*lane,k),k.two72);
Rd::run(Lo { v:upcast(lo) },kd,ref coeffs);
}
}
#[cfg(test)]
mod lane_reader_tests {
use corelib_imports::bounded_int::upcast;
use super::{MsgCoeff,push_block_fast,push_block_lanes_raw,squeeze_consts};
use super::super::shake256::keccak_f1600_packed;
#[test]
fn test_lane_reader_matches_block_reader_falcon_512_shake() {
let k=squeeze_consts();
let mut st:[u128; 13]=[1,2,3,4,5,6,7,8,9,10,0xffffffffffffffffffffffffffffffff,12,13];
let mut round=0_u32;
while round != 6 {
st=keccak_f1600_packed(st);
for start in array![0_u32,400,444,445,480,500,508,511] {
let mut a:Array<MsgCoeff> = array![];
let mut b:Array<MsgCoeff> = array![];
let mut i=0;
while i != start {
a.append(0);
b.append(0);
i += 1;
}
let [s0,s1,s2,s3,_,s5,s6,s7,s8,_,s10,s11,_]=st;
let lanes=[s0,s1,s2,s3,s5,s6,s7,s8,s10,s11];
push_block_fast(@lanes,ref a,k);
push_block_lanes_raw(@lanes,ref b,k,true);
let n=if a.len() < b.len() { a.len() } else { b.len() };
assert(n >= 512 || a.len() == b.len(), 'lane reader len');
let mut j=0;
while j != n {
let x:u64=upcast(*a[j]);
let y:u64=upcast(*b[j]);
assert(x % 12289 == y % 12289, 'lane reader');
j += 1;
}
}
round += 1;
}
}
}
#[cfg(test)]
mod syscall_tail_tests {
use corelib_imports::bounded_int::upcast;
use super::{hash_to_point_shake_512,hash_to_point_shake_512_raw_tail};
fn check(mh:felt252,sa:felt252,sb:felt252) {
let reduced=hash_to_point_shake_512(mh,sa,sb).unwrap();
for tail in array![0_u32,15,68,512] {
let raw=hash_to_point_shake_512_raw_tail(mh,sa,sb,tail).unwrap();
assert(raw.len() >= 512, 'len');
let mut i=0;
while i != 512 {
let r:u64=upcast(*raw[i]);
let c:u64=(*reduced[i]).into();
assert(r % 12289 == c, 'coeff');
i += 1;
}
}
}
#[test]
fn test_syscall_tail_falcon_512_shake() {
check(0x1234,0x5678,0x9abc);
check(
0x7ff0123456789abcdef0123456789abcdef0123456789abcdef0123456789ab,
0xffffffffffffffffffffffffffffffffffffffff,
0xfedcba9876543210fedcba9876543210fedcba98,
);
check(1,2,3);
check(0xdeadbeef,0,0xffffffffffffffffffffffffffffffffffffffff);
check(42,0x0123456789abcdef0123456789abcdef01234567,7);
}
}
