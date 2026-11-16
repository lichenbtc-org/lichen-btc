//! RISC Zero 3.1's Groth16 statement checked natively: whether a proof's
//! points prove that a guest `image_id` halted with exit code 0 and wrote
//! `journal`, under RISC Zero 3.1's verifying key, control root and BN254
//! control id. Lichen's BABE gadget is built on this key and these public
//! inputs; this module also decides a proof in milliseconds.
//!
//! The points are compressed in FairgateLabs' convention (each x
//! little-endian, the top bit of its last byte set iff y is odd; B as x.c0
//! then x.c1, the flag from y.c0). [`split_input`] reads the package their
//! `proof-as-input` writes: the journal's length in words (u32 LE), the
//! image id, the three points, then the journal.
//!
//! The verifying key, the control root and id, and the claim's hashing are
//! RISC Zero's (risc0-groth16 3.0.6, risc0-circuit-recursion 4.1.0,
//! risc0-zkvm 3.1.0, risc0-binfmt 3.0.6; Apache-2.0), reproduced here so
//! the workspace needn't depend on RISC Zero; the pairing is arkworks'.

use anyhow::{ensure, Context, Result};
use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, Field, PrimeField};
use sha2::{Digest as _, Sha256};
use std::str::FromStr;

/// RISC Zero 3.1's recursion control root (`ALLOWED_CONTROL_ROOT`).
pub const CONTROL_ROOT: &str = "e6feef13db7aed4a731c7b0852de1f5c89b137726073f625d05333184d3a551d";
/// RISC Zero 3.1's BN254 identity control id (`BN254_IDENTITY_CONTROL_ID`).
pub const BN254_CONTROL_ID: &str = "de81d091ba14062acb5023b3b36deee95624e3fd47475cb7ff64aed5f9eac20a";

/// The verifying key of RISC Zero 3.1's Groth16 circuit (risc0-groth16
/// 3.0.6, from risc0-ethereum's Groth16Verifier.sol), as decimal
/// coordinates; G2 coordinates as `(c1, c0)`.
const ALPHA: [&str; 2] = ["16428432848801857252194528405604668803277877773566238944394625302971855135431", "16846502678714586896801519656441059708016666274385668027902869494772365009666"];
const BETA: [&str; 4] = [
    "3182164110458002340215786955198810119980427837186618912744689678939861918171",
    "16348171800823588416173124589066524623406261996681292662100840445103873053252",
    "4920802715848186258981584729175884379674325733638798907835771393452862684714",
    "19687132236965066906216944365591810874384658708175106803089633851114028275753",
];
const GAMMA: [&str; 4] = [
    "11559732032986387107991004021392285783925812861821192530917403151452391805634",
    "10857046999023057135944570762232829481370756359578518086990519993285655852781",
    "4082367875863433681332203403145435568316851327593401208105741076214120093531",
    "8495653923123431417604973247489272438418190587263600148770280649306958101930",
];
const DELTA: [&str; 4] = [
    "15616655295497688016920922285786248029410410634174255119755032442279507261612",
    "15776672394616990683767400715354533957990327248900631669473166016258279232588",
    "15603769682755083227316504195454390494226357053638046843688553601570183264395",
    "6666730711543397578682474175129345128534747409410156889826997147291122518312",
];
const IC: [[&str; 2]; 6] = [
    ["18663918579753010382002747204100316475180663666125247285366810668134508578264", "17189072794432247265173990289507014998311702955803346313941168113828133843434"],
    ["10995657406716404592042449088731908804822551193011116024160605390904112699922", "16840054500543522560166231854936072122401577171365452702445604851845250658027"],
    ["17223746139751910493708334502747005647365937123243899090309734281916083451762", "4092210736358501801028887881307062309243791997444282548134854129284894411044"],
    ["3765213192101990618643617040373059738050185238026301923348610794767426428033", "12210223264334159465299028585581460715942724522871187397965100355295734194591"],
    ["10211980968769599651826920300372241897389214017084266564307091587192484525770", "6627619408770540710319105693121261544533216204749218194792386277379533604252"],
    ["13454640350766589059799184485082639692652215534373479852236969801352010275184", "8731676129773990833613417922371950977268622282768299686490610454524284784606"],
];

fn sha256(b: &[u8]) -> [u8; 32] {
    Sha256::digest(b).into()
}

/// RISC Zero's tagged struct hash (`risc0_binfmt::tagged_struct`).
fn tagged(tag: &str, down: &[[u8; 32]], data: &[u32]) -> [u8; 32] {
    let mut all = sha256(tag.as_bytes()).to_vec();
    for d in down {
        all.extend_from_slice(d);
    }
    for w in data {
        all.extend_from_slice(&w.to_le_bytes());
    }
    all.extend_from_slice(&(down.len() as u16).to_le_bytes());
    sha256(&all)
}

/// The digest of RISC Zero's receipt claim for a guest that halted with
/// exit code 0 (`ReceiptClaim::ok(image_id, journal)`): its input none,
/// its pre-state pruned to the image id, its post-state at pc 0 with a
/// zero root, its output the journal with no assumptions.
pub fn claim_digest(image_id: &[u8; 32], journal: &[u8]) -> [u8; 32] {
    let zero = [0u8; 32];
    let post = tagged("risc0.SystemState", &[zero], &[0]);
    let output = tagged("risc0.Output", &[sha256(journal), zero], &[]);
    tagged("risc0.ReceiptClaim", &[zero, *image_id, post, output], &[0, 0])
}

/// The proof's public inputs: the control root's halves, the claim's
/// halves (each half a little-endian integer), the BN254 control id
/// (likewise).
pub fn public_inputs(claim: &[u8; 32]) -> [Fr; 5] {
    let root = hex::decode(CONTROL_ROOT).expect("hex");
    let id = hex::decode(BN254_CONTROL_ID).expect("hex");
    let le = Fr::from_le_bytes_mod_order;
    [le(&root[..16]), le(&root[16..]), le(&claim[..16]), le(&claim[16..]), le(&id)]
}

fn dec(s: &str) -> Fq {
    Fq::from_str(s).ok().expect("a field element")
}

fn g1_const(c: [&str; 2]) -> G1Affine {
    G1Affine::new(dec(c[0]), dec(c[1]))
}

fn g2_const(c: [&str; 4]) -> G2Affine {
    G2Affine::new(Fq2::new(dec(c[1]), dec(c[0])), Fq2::new(dec(c[3]), dec(c[2])))
}

/// RISC Zero 3.1's verifying key, as points: `ic` the public inputs'
/// bases, the constant's first.
pub struct Key {
    pub alpha: G1Affine,
    pub beta: G2Affine,
    pub gamma: G2Affine,
    pub delta: G2Affine,
    pub ic: [G1Affine; 6],
}

pub fn key() -> Key {
    Key { alpha: g1_const(ALPHA), beta: g2_const(BETA), gamma: g2_const(GAMMA), delta: g2_const(DELTA), ic: IC.map(g1_const) }
}

/// A Groth16 proof's points.
pub struct Proof {
    pub a: G1Affine,
    pub b: G2Affine,
    pub c: G1Affine,
}

/// A base field element from 32 little-endian bytes, below the modulus.
fn fq_le(b: &[u8]) -> Result<Fq> {
    let x = Fq::from_le_bytes_mod_order(b);
    ensure!(x.into_bigint().to_bytes_le() == b, "a coordinate beyond the field");
    Ok(x)
}

fn odd(y: Fq) -> bool {
    y.into_bigint().is_odd()
}

/// A G1 point from 32 bytes in Fairgate's convention.
fn g1(b: &[u8]) -> Result<G1Affine> {
    let mut x = b.to_vec();
    let flag = x[31] & 0x80 != 0;
    x[31] &= 0x7f;
    let x = fq_le(&x)?;
    let (y, minus) = G1Affine::get_ys_from_x_unchecked(x).context("a G1 x off the curve")?;
    let p = G1Affine::new_unchecked(x, if odd(y) == flag { y } else { minus });
    ensure!(p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve(), "not a G1 point");
    Ok(p)
}

/// A G2 point from 64 bytes in Fairgate's convention.
fn g2(b: &[u8]) -> Result<G2Affine> {
    let mut c1 = b[32..].to_vec();
    let flag = c1[31] & 0x80 != 0;
    c1[31] &= 0x7f;
    let x = Fq2::new(fq_le(&b[..32])?, fq_le(&c1)?);
    let (y, minus) = G2Affine::get_ys_from_x_unchecked(x).context("a G2 x off the curve")?;
    let p = G2Affine::new_unchecked(x, if odd(y.c0) == flag { y } else { minus });
    ensure!(p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve(), "not a G2 point");
    Ok(p)
}

/// The points of a proof compressed (A, B, C: 128 bytes).
pub fn decode(points: &[u8]) -> Result<Proof> {
    ensure!(points.len() == 128, "the proof is 128 bytes, not {}", points.len());
    Ok(Proof { a: g1(&points[..32])?, b: g2(&points[32..96])?, c: g1(&points[96..])? })
}

/// Whether `points` (A, B, C compressed: 128 bytes) prove that the guest
/// `image_id` halted with exit code 0 and wrote `journal`.
pub fn verify(image_id: &[u8; 32], points: &[u8], journal: &[u8]) -> Result<()> {
    let Proof { a, b, c } = decode(points)?;
    let k = key();
    let inputs = public_inputs(&claim_digest(image_id, journal));
    let mut vk_x = G1Projective::from(k.ic[0]);
    for (x, ic) in inputs.iter().zip(&k.ic[1..]) {
        vk_x += *ic * x;
    }
    // e(A, B) = e(alpha, beta) e(vk_x, gamma) e(C, delta)
    let check = Bn254::multi_pairing([a, -k.alpha, -vk_x.into_affine(), -c], [b, k.beta, k.gamma, k.delta]);
    ensure!(check.0 == <Bn254 as Pairing>::TargetField::ONE, "the proof doesn't verify");
    Ok(())
}

/// A proof package split (FairgateLabs' `proof-as-input`): the image id, the proof's points
/// (compressed, 128 bytes), the journal.
pub fn split_input(input: &[u8]) -> Result<([u8; 32], &[u8], &[u8])> {
    ensure!(input.len() >= 164, "an input of {} bytes", input.len());
    let n = u32::from_le_bytes(input[..4].try_into().unwrap()) as usize;
    ensure!(input.len() == 164 + 4 * n, "a journal of {n} words in an input of {} bytes", input.len());
    Ok((input[4..36].try_into().unwrap(), &input[36..164], &input[164..]))
}

/// Whether a proof package (as [`split_input`] reads it) verifies.
pub fn verify_input(input: &[u8]) -> Result<()> {
    let (image_id, points, journal) = split_input(input)?;
    verify(&image_id, points, journal)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A withdrawal guest's receipt (ln-gap's, where this crate began): a
    /// return of 9 sats with memo 42.
    fn withdraw_9_42() -> Vec<u8> {
        hex::decode(include_str!("../tests/data/withdraw-9-42.hex").trim()).unwrap()
    }

    /// The current statement, on the toy deployment's return of 9 with memo 42.
    fn withdraw_9_42_deployment() -> Vec<u8> {
        hex::decode(include_str!("../tests/data/withdraw-9-42-deployment.hex").trim()).unwrap()
    }

    /// The placeholder guest's receipt on (9, 42) under RISC Zero 3.0, as
    /// FairgateLabs' `proof-as-input` encodes it.
    const PLACEHOLDER_R0_3_0: &str = "02000000c2bf393e7d9cbb53a5b6f0c1bc9767d42c04f632a9824a572eb7a5d6d77cd25055980d21b8181f697bec1fd16580c85509250218b39ecac0d3f2b8f55f456a1cd0838280b11c1fb7575a9a808d95d08a3431af29793cd1d444f0a9c6c56e3f109fcca45f4f0a79fe1dbf43f70bcd73560644f679d3852ab8fea067548d7c189d523bd82d59a760a5b05757fca4743552bb0717eb0be71a060e2b37877d343410090000002a000000";

    #[test]
    fn verifies_good_receipts() {
        for (name, input) in [("withdraw-9-42", withdraw_9_42()), ("withdraw-9-42-deployment", withdraw_9_42_deployment())] {
            let t = std::time::Instant::now();
            verify_input(&input).unwrap_or_else(|e| panic!("{name}: {e:#}"));
            println!("GROTH16 {name}: verified natively in {:.1?}", t.elapsed());
        }
    }

    #[test]
    fn rejects_a_receipt_made_under_risc_zero_3_0() {
        assert!(verify_input(&hex::decode(PLACEHOLDER_R0_3_0).unwrap()).is_err(), "a 3.0 receipt verifies under 3.1's key");
    }

    #[test]
    fn rejects_what_it_doesnt() {
        let good = withdraw_9_42();
        let edit = |at: usize, x: u8| {
            let mut v = good.clone();
            v[at] ^= x;
            v
        };
        // b (the journal's first word), the image id, each point's x and
        // flag, the journal's length
        for (what, input) in [("b", edit(164, 3)), ("the image id", edit(4, 1)), ("A", edit(36, 1)), ("A's flag", edit(67, 0x80)), ("B", edit(68, 1)), ("B's flag", edit(131, 0x80)), ("C", edit(132, 1)), ("the length", edit(0, 1))] {
            assert!(verify_input(&input).is_err(), "{what} changed, yet it verifies");
        }
    }
}
