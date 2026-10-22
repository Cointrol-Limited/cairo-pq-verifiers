//! Base-q packing of 1024 coefficients into 57 felts, as the Falcon-512 season's layout packs 512
//! into 29: each felt is pack9(low) + 2^128 * pack9(high), base q with the first coefficient least
//! significant, and the last felt holds sixteen, nine low and seven high. Unpacking refuses any
//! half whose digits leave a remainder, so every key and signature has one encoding.

pub const SLOTS: u32 = 57;
const FULL_SLOTS: u32 = 56;
const Q: NonZero<u128> = 12289;

/// The 1024 coefficients in [0, q) packed in `packed`, or None for a wrong length or a
/// non-canonical felt.
pub fn unpack_1024(packed: Span<felt252>) -> Option<Array<felt252>> {
    if packed.len() != SLOTS {
        return None;
    }
    let mut out: Array<felt252> = array![];
    let mut slot: u32 = 0;
    let mut canonical = true;
    for felt in packed {
        let value: u256 = (*felt).into();
        let high = if slot == FULL_SLOTS {
            7
        } else {
            9
        };
        if digits(value.low, 9, ref out) != 0 || digits(value.high, high, ref out) != 0 {
            canonical = false;
            break;
        }
        slot += 1;
    }
    if canonical {
        Some(out)
    } else {
        None
    }
}

/// Append `count` base-q digits of `value`, least significant first, and return what is left.
fn digits(value: u128, count: u32, ref out: Array<felt252>) -> u128 {
    let mut rest = value;
    let mut k = 0;
    while k != count {
        let (above, digit) = DivRem::div_rem(rest, Q);
        out.append(digit.into());
        rest = above;
        k += 1;
    }
    rest
}
