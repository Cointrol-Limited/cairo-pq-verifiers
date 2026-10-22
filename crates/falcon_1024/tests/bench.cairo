//! Benchmark scenarios for the Falcon-1024 verifier: one falcon.py key and its signature on
//! 'BENCH_MSG', and the same inputs without the verification, for the baseline cost of building
//! them.

use pqbench_falcon_1024::Falcon1024Verifier;
use pqbench_falcon_1024::fixtures::shake::{msg, public_key, signature};
use pqbench_interface::PqSignatureVerifier;

#[test]
fn bench_baseline_falcon_1024() {
    let pk = public_key();
    let sig = signature();
    assert!(pk.len() == 57 && sig.len() == 116 && msg() != 0);
}

#[test]
fn bench_verify_falcon_1024() {
    let pk = public_key();
    let sig = signature();
    assert!(Falcon1024Verifier::verify(msg(), pk.span(), sig.span()));
}
