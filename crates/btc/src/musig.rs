//! MuSig2 (BIP327) over bitcoin's types: a key path that several parties
//! sign together, the output looking like any single-key taproot output
//! and its spend like any single-key spend.
//!
//! Keys are x-only (BIP340), lifted to even y for the aggregation; a
//! signer whose key pair has odd y signs with its secret negated, as
//! BIP340 does. The aggregate is taken in the order given (BIP327's
//! `KeyAgg`, not sorted): every party must list the keys alike.
//!
//! A signing session, two rounds: each party makes a nonce ([`nonce`])
//! and shares its public half; each signs ([`sign`], which consumes its
//! secret half) and shares its partial signature; anyone combines them
//! ([`aggregate`]). A secret nonce must sign at most once: [`SecNonce`]
//! is neither `Clone` nor serializable, so it lives in one process, for
//! one signature.
//!
//! The arithmetic is conduition's `musig2` crate (k256 backend, so that
//! its secp256k1 version doesn't have to match bitcoin's).

use anyhow::{anyhow, ensure, Context, Result};
use bitcoin::key::{Keypair, Parity, XOnlyPublicKey};
use bitcoin::secp256k1::{schnorr, Message, SECP256K1};
use bitcoin::taproot::TapNodeHash;
use musig2::secp::{MaybeScalar, Point, Scalar};
use musig2::{AggNonce, BinaryEncoding, CompactSignature, KeyAggContext, PartialSignature};
use rand::RngCore;

/// The aggregate of several x-only keys, untweaked or tweaked for taproot.
#[derive(Clone, Debug)]
pub struct KeyAgg {
    ctx: KeyAggContext,
}

fn point(key: &XOnlyPublicKey) -> Result<Point> {
    let mut b = [2u8; 33];
    b[1..].copy_from_slice(&key.serialize());
    Point::from_slice(&b).map_err(|e| anyhow!("{key}: not a point: {e}"))
}

fn xonly(p: Point) -> XOnlyPublicKey {
    XOnlyPublicKey::from_slice(&p.serialize_xonly()).expect("a point's x")
}

/// The secret key that signs for `kp`'s x-only key (negated at odd y).
fn signing_key(kp: &Keypair) -> Result<Scalar> {
    let sk = match kp.x_only_public_key().1 {
        Parity::Even => kp.secret_key(),
        Parity::Odd => kp.secret_key().negate(),
    };
    Scalar::from_slice(&sk.secret_bytes()).map_err(|e| anyhow!("a secret key: {e}"))
}

impl KeyAgg {
    /// The keys' aggregate, in the order given.
    pub fn new(keys: &[XOnlyPublicKey]) -> Result<KeyAgg> {
        ensure!(!keys.is_empty(), "no keys to aggregate");
        let points = keys.iter().map(point).collect::<Result<Vec<_>>>()?;
        Ok(KeyAgg { ctx: KeyAggContext::new(points).map_err(|e| anyhow!("aggregating keys: {e}"))? })
    }
    /// The untweaked aggregate: a taproot output's internal key.
    pub fn internal_key(&self) -> XOnlyPublicKey {
        xonly(self.ctx.aggregated_pubkey_untweaked())
    }
    /// Tweaked as BIP341 tweaks an internal key with the script tree's
    /// root (`None`: no script tree), so that it signs for the output key.
    pub fn taproot(&self, merkle_root: Option<TapNodeHash>) -> Result<KeyAgg> {
        let ctx = match merkle_root {
            Some(root) => self.ctx.clone().with_taproot_tweak(root.as_ref()),
            None => self.ctx.clone().with_unspendable_taproot_tweak(),
        }
        .map_err(|e| anyhow!("the taproot tweak: {e}"))?;
        Ok(KeyAgg { ctx })
    }
    /// The key the aggregate signs for (the output key, once tweaked).
    pub fn output_key(&self) -> XOnlyPublicKey {
        xonly(self.ctx.aggregated_pubkey())
    }
}

/// A secret nonce: signs once, in this process.
pub struct SecNonce(musig2::SecNonce);

impl std::fmt::Debug for SecNonce {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SecNonce(..)")
    }
}

/// A public nonce (two points, 66 bytes), shared with the other signers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PubNonce(pub [u8; 66]);

impl PubNonce {
    pub fn from_slice(b: &[u8]) -> Result<PubNonce> {
        let n = musig2::PubNonce::from_bytes(b).map_err(|e| anyhow!("a public nonce: {e}"))?;
        Ok(PubNonce(n.to_bytes()))
    }
    fn inner(&self) -> musig2::PubNonce {
        musig2::PubNonce::from_bytes(&self.0).expect("checked when made")
    }
}

/// A partial signature (a scalar, 32 bytes).
pub type Partial = [u8; 32];

/// A fresh nonce for `kp` signing under `agg` (the tweaked aggregate):
/// BIP327's generation, from 32 random bytes, the secret key, the
/// aggregate key and `extra` (the session's context, such as what is to
/// be signed and for whom).
pub fn nonce(agg: &KeyAgg, kp: &Keypair, extra: &[u8]) -> Result<(SecNonce, PubNonce)> {
    let mut seed = [0u8; 32];
    rand::rngs::OsRng.fill_bytes(&mut seed);
    let agg_pk: Point = agg.ctx.aggregated_pubkey();
    let sec = musig2::SecNonce::build_with_seckey(seed, signing_key(kp)?).with_aggregated_pubkey(agg_pk).with_extra_input(&extra).build();
    let public = PubNonce(sec.public_nonce().to_bytes());
    Ok((SecNonce(sec), public))
}

fn agg_nonce(nonces: &[PubNonce]) -> AggNonce {
    AggNonce::sum(nonces.iter().map(PubNonce::inner))
}

/// `kp`'s partial signature on `msg` under `agg`, its nonce `sec` (spent
/// here) among `nonces` (every signer's, its own included).
pub fn sign(agg: &KeyAgg, kp: &Keypair, sec: SecNonce, nonces: &[PubNonce], msg: &[u8; 32]) -> Result<Partial> {
    let s: PartialSignature = musig2::sign_partial(&agg.ctx, signing_key(kp)?, sec.0, &agg_nonce(nonces), msg).map_err(|e| anyhow!("signing: {e}"))?;
    Ok(s.serialize())
}

/// Check `key`'s partial signature `partial` on `msg`, its nonce `nonce`
/// among `nonces`.
pub fn verify_partial(agg: &KeyAgg, key: &XOnlyPublicKey, nonce: &PubNonce, nonces: &[PubNonce], partial: &Partial, msg: &[u8; 32]) -> Result<()> {
    let s = MaybeScalar::from_slice(partial).map_err(|e| anyhow!("a partial signature: {e}"))?;
    musig2::verify_partial(&agg.ctx, s, &agg_nonce(nonces), point(key)?, &nonce.inner(), msg).map_err(|e| anyhow!("{key}'s partial signature: {e}"))
}

/// The signature the partial signatures make, checked under the
/// aggregate's output key.
pub fn aggregate(agg: &KeyAgg, nonces: &[PubNonce], partials: &[Partial], msg: &[u8; 32]) -> Result<schnorr::Signature> {
    let parts = partials.iter().map(|p| MaybeScalar::from_slice(p).map_err(|e| anyhow!("a partial signature: {e}"))).collect::<Result<Vec<_>>>()?;
    let sig: CompactSignature = musig2::aggregate_partial_signatures(&agg.ctx, &agg_nonce(nonces), parts, msg).map_err(|e| anyhow!("aggregating: {e}"))?;
    let sig = schnorr::Signature::from_slice(&sig.to_bytes()).context("a signature")?;
    SECP256K1.verify_schnorr(&sig, &Message::from_digest(*msg), &agg.output_key()).context("the aggregate signature")?;
    Ok(sig)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keys::Seed;
    use crate::taptree::{Leaf, TapTree};
    use crate::tx::Timelock;
    use bitcoin::script::Builder;

    fn kps() -> Vec<Keypair> {
        // labels until both parities appear among the keys
        (0..8).map(|i| Seed::from_label(&format!("musig/{i}")).keypair("k")).collect()
    }

    #[test]
    fn the_aggregate_is_the_tree_s_internal_key_and_signs_for_its_output() {
        let kps = kps();
        assert!(kps.iter().any(|k| k.x_only_public_key().1 == Parity::Odd) && kps.iter().any(|k| k.x_only_public_key().1 == Parity::Even), "both parities");
        for pair in kps.windows(2) {
            let keys: Vec<_> = pair.iter().map(|k| k.x_only_public_key().0).collect();
            let agg = KeyAgg::new(&keys).unwrap();
            let leaf = Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE);
            let tree = TapTree::with_internal_key(agg.internal_key(), vec![leaf]).unwrap();
            let tweaked = agg.taproot(tree.merkle_root()).unwrap();
            assert_eq!(tweaked.output_key(), tree.output_key().to_x_only_public_key());
            let msg = [7u8; 32];
            let (s0, n0) = nonce(&tweaked, &pair[0], b"test").unwrap();
            let (s1, n1) = nonce(&tweaked, &pair[1], b"test").unwrap();
            let nonces = [n0, n1];
            let p0 = sign(&tweaked, &pair[0], s0, &nonces, &msg).unwrap();
            let p1 = sign(&tweaked, &pair[1], s1, &nonces, &msg).unwrap();
            verify_partial(&tweaked, &keys[0], &n0, &nonces, &p0, &msg).unwrap();
            verify_partial(&tweaked, &keys[1], &n1, &nonces, &p1, &msg).unwrap();
            assert!(verify_partial(&tweaked, &keys[1], &n1, &nonces, &p0, &msg).is_err(), "one party's partial as the other's");
            assert!(verify_partial(&tweaked, &keys[0], &n0, &nonces, &p0, &[8u8; 32]).is_err(), "another message");
            aggregate(&tweaked, &nonces, &[p0, p1], &msg).unwrap();
            assert!(aggregate(&tweaked, &nonces, &[p0, p0], &msg).is_err());
        }
    }

    #[test]
    fn without_a_tree_it_signs_for_bip86_s_output_key() {
        let kps = kps();
        let keys: Vec<_> = kps[..3].iter().map(|k| k.x_only_public_key().0).collect();
        let agg = KeyAgg::new(&keys).unwrap().taproot(None).unwrap();
        let expect = bitcoin::taproot::TaprootSpendInfo::new_key_spend(SECP256K1, KeyAgg::new(&keys).unwrap().internal_key(), None).output_key().to_x_only_public_key();
        assert_eq!(agg.output_key(), expect);
        let msg = [1u8; 32];
        let made: Vec<_> = kps[..3].iter().map(|k| nonce(&agg, k, b"").unwrap()).collect();
        let nonces: Vec<_> = made.iter().map(|m| m.1).collect();
        let parts: Vec<_> = made.into_iter().zip(&kps[..3]).map(|((s, _), k)| sign(&agg, k, s, &nonces, &msg).unwrap()).collect();
        aggregate(&agg, &nonces, &parts, &msg).unwrap();
    }
}
