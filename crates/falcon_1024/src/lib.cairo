//! Falcon-1024 (FN-DSA at NIST's level 5) signature verification for Starknet.
//!
//! `Falcon1024Verifier::verify` checks a Falcon-1024 signature over the transaction hash in the
//! Falcon-512 season's hint layout, at n = 1024:
//!
//! - the public key is the NTT-domain key h packed base q, 57 felts;
//! - the signature is packed s1 (57 felts) || the 40-byte salt as two 20-byte little-endian felts
//!   || packed mul_hint = s1 * h (57 felts);
//! - the message point is the standard SHAKE-256 hash-to-point of salt || the felt's 32
//!   little-endian bytes.
//!
//! A signature is valid when NTT(s1) * h_ntt == NTT(mul_hint) pointwise mod q, which binds the
//! hint to s1 * h, and ||message point - mul_hint||^2 + ||s1||^2 <= 70,265,242 over centered
//! coefficients. Checked against falcon.py (tests/).

pub mod falcon;
pub mod fixtures;
pub mod hash_to_point;
pub mod keccak;
pub mod ntt;
pub mod packing;
use pqbench_interface::PqSignatureVerifier;

pub const PUBKEY_FELTS: u32 = 57;
pub const SIG_FELTS: u32 = 116;

pub impl Falcon1024Verifier of PqSignatureVerifier {
    fn verify(message_hash: felt252, public_key: Span<felt252>, signature: Span<felt252>) -> bool {
        if public_key.len() != PUBKEY_FELTS || signature.len() != SIG_FELTS {
            return false;
        }
        let h_ntt = match packing::unpack_1024(public_key) {
            Some(v) => v,
            None => { return false; },
        };
        let s1 = match packing::unpack_1024(signature.slice(0, 57)) {
            Some(v) => v,
            None => { return false; },
        };
        let mul_hint = match packing::unpack_1024(signature.slice(59, 57)) {
            Some(v) => v,
            None => { return false; },
        };
        let point =
            match hash_to_point::hash_to_point(message_hash, *signature.at(57), *signature.at(58)) {
            Some(v) => v,
            None => { return false; },
        };
        falcon::verify_with_hint(s1.span(), h_ntt.span(), mul_hint.span(), point.span())
    }
}
