//! A multi-party setup ceremony for the proven-input CRS, so that no single
//! party knows its trapdoor.
//!
//! The CRS is a list of powers of a secret `α`: `g_p = α^p·g` for
//! `p ∈ [1, 2n] \ {n+1}` (`g_{n+1} = 0`) and `ĝ_p = α^p·ĝ` for `p ∈ [1, n]`.
//! Whoever knows `α` can forge proofs of encryption. The ceremony starts from
//! `α = 1`, which anyone can check, and each contributor `i` multiplies every
//! `g_p` and `ĝ_p` by `τ_i^p` for a fresh secret `τ_i`, then forgets it. The
//! result has `α = Π τ_i`: unknown unless every contributor colludes.
//!
//! A contribution publishes `h_i = τ_i·ĝ`, the new `g_1`, and a Schnorr proof
//! of knowledge of `τ_i` whose challenge binds the previous `g_1`, so it
//! cannot be copied from another contributor or replayed elsewhere in the
//! chain. [`verify`] checks, with pairings `e`:
//!
//! - every point lies in its prime-order subgroup;
//! - the chain: `g_1^(0) = g`, `e(g_1^(i), ĝ) = e(g_1^(i-1), h_i)`, `h_i ≠ 0`,
//!   each proof of knowledge, and that the CRS's `g_1` is the last link;
//! - the structure: the CRS is the powers of the one `α` that `g_1` fixes,
//!   in a random linear combination of the per-power pairing equations.
//!
//! The chain shows that each `τ_i` was known to someone, not to whom: a
//! coordinator could run every contribution itself. So a contributor may
//! sign its receipt with a long-term identity key ([`keygen`]); the receipt
//! binds the contribution and its place in the chain, so the signature
//! cannot be moved to another one. [`verify`] checks every signature, and
//! given the public keys of parties the verifier trusts, requires one of
//! them to have signed a contribution: if that party discarded its `τ`, no
//! one knows the trapdoor.
//!
//! The ceremony lives in a directory: `crs.bin` (what `publish` adopts and
//! `tclmesh-tfhe-prove` reads) and `ceremony.json` (the contributions).
//! Points cross the TFHE-rs serialization boundary as JSON, through
//! [`Crs`], which mirrors `CompactPkeCrs::PkeV2` and passes every field but
//! the points through untouched.

use crate::{config, load, save, CRS, CRS_MAX_BITS};
use rand::RngCore;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;
use std::path::Path;
use tfhe::zk::CompactPkeCrs;
use tfhe_zk_pok::curve_api::bls12_446::{Gt, Zp, G1, G2};
use tfhe_zk_pok::curve_api::CurveGroupOps;

pub const TRANSCRIPT: &str = "ceremony.json";
const VERSION: &str = "tclmesh-crs-ceremony-v1";
const SIGNATURE: &str = "tclmesh-crs-contribution-signature-v1";

/// `CompactPkeCrs`, with the points typed.
#[derive(Serialize, Deserialize)]
enum Crs {
    PkeV2(Params),
}

#[allow(non_snake_case)]
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Params {
    g_lists: Lists,
    n: usize,
    D: Box<RawValue>,
    d: Box<RawValue>,
    k: Box<RawValue>,
    B_bound_squared: Box<RawValue>,
    B_inf: Box<RawValue>,
    q: Box<RawValue>,
    t: Box<RawValue>,
    msbs_zero_padding_bit_count: Box<RawValue>,
    bound_type: Box<RawValue>,
    sid: Box<RawValue>,
    domain_separators: Box<RawValue>,
}

/// `g_list[p - 1] = g_p`, `g_hat_list[p - 1] = ĝ_p`.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Lists {
    g_list: Vec<G1>,
    g_hat_list: Vec<G2>,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Contribution {
    /// `g_1` after this contribution.
    g1: G1,
    /// `τ·ĝ`.
    h: G2,
    /// Schnorr proof of knowledge of `τ`: `r = k·ĝ`, `s = k + c·τ`.
    r: G2,
    s: Zp,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    signature: Option<Signature>,
}

/// A Schnorr signature by `signer = sk·g` on a receipt: `r = k·g`,
/// `s = k + e·sk` for `e = H(signer, r, receipt)`.
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Signature {
    signer: G1,
    r: G1,
    s: Zp,
}

/// A contributor's long-term signing key.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SecretKey {
    secret: Zp,
}

/// The public half of a [`SecretKey`]: what a verifier trusts.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublicKey {
    public: G1,
}

impl PublicKey {
    /// A short, stable name for the key.
    pub fn fingerprint(&self) -> String {
        hex(digest(&[SIGNATURE.as_bytes(), &self.public.to_le_bytes()]))
    }
}

/// A contribution's receipt, and the fingerprint of its signer if signed.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Receipt {
    pub receipt: String,
    pub signer: Option<String>,
}

impl std::fmt::Display for Receipt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {}",
            self.receipt,
            self.signer.as_deref().unwrap_or("-")
        )
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Transcript {
    version: String,
    contributions: Vec<Contribution>,
}

fn to_params(crs: &CompactPkeCrs) -> Result<Params, String> {
    let json = serde_json::to_string(crs).map_err(|e| e.to_string())?;
    match serde_json::from_str(&json).map_err(|e| format!("unsupported CRS: {e}"))? {
        Crs::PkeV2(p) => Ok(p),
    }
}

fn from_params(params: Params) -> Result<CompactPkeCrs, String> {
    let json = serde_json::to_string(&Crs::PkeV2(params)).map_err(|e| e.to_string())?;
    serde_json::from_str(&json).map_err(|e| e.to_string())
}

fn digest(data: &[&[u8]]) -> Zp {
    let mut out = [Zp::ZERO];
    Zp::hash(&mut out, data);
    out[0]
}

fn hex(x: Zp) -> String {
    x.to_le_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

/// The challenge of contribution `index`, which follows `prev`.
fn challenge(index: usize, prev: G1, c: &Contribution) -> Zp {
    digest(&[
        VERSION.as_bytes(),
        &(index as u64).to_le_bytes(),
        &prev.to_le_bytes(),
        &c.g1.to_le_bytes(),
        &c.h.to_le_bytes(),
        &c.r.to_le_bytes(),
    ])
}

/// A contribution's receipt: its challenge, which binds all of it and its
/// place in the chain. A contributor checks that [`verify`] lists theirs.
fn receipt(index: usize, prev: G1, c: &Contribution) -> String {
    hex(challenge(index, prev, c))
}

/// The signature challenge on `receipt`.
fn signed(signer: G1, r: G1, receipt: &str) -> Zp {
    digest(&[
        SIGNATURE.as_bytes(),
        &signer.to_le_bytes(),
        &r.to_le_bytes(),
        receipt.as_bytes(),
    ])
}

fn sign(key: &SecretKey, receipt: &str, rng: &mut dyn RngCore) -> Signature {
    let (signer, k) = (G1::GENERATOR.mul_scalar(key.secret), Zp::rand(rng));
    let r = G1::GENERATOR.mul_scalar(k);
    Signature {
        signer,
        r,
        s: k + signed(signer, r, receipt) * key.secret,
    }
}

fn signature_ok(sig: &Signature, receipt: &str) -> bool {
    sig.signer != G1::ZERO
        && G1::GENERATOR.mul_scalar(sig.s)
            == sig.r + sig.signer.mul_scalar(signed(sig.signer, sig.r, receipt))
}

/// A fresh signing key and its public half.
pub fn keygen(rng: &mut dyn RngCore) -> (SecretKey, PublicKey) {
    let secret = Zp::rand(rng);
    let public = G1::GENERATOR.mul_scalar(secret);
    (SecretKey { secret }, PublicKey { public })
}

fn json<T: Serialize>(value: &T) -> String {
    serde_json::to_string(value).expect("keys serialize")
}

fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))
}

/// Write a fresh key pair: the secret readable by its owner only, and never
/// over an existing file.
pub fn write_keys(
    secret: &Path,
    public: &Path,
    rng: &mut dyn RngCore,
) -> Result<PublicKey, String> {
    use std::io::Write;
    use std::os::unix::fs::OpenOptionsExt;
    let (sk, pk) = keygen(rng);
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(secret)
        .and_then(|mut f| f.write_all(json(&sk).as_bytes()))
        .map_err(|e| format!("{}: {e}", secret.display()))?;
    std::fs::write(public, json(&pk)).map_err(|e| format!("{}: {e}", public.display()))?;
    Ok(pk)
}

pub fn read_secret(path: &Path) -> Result<SecretKey, String> {
    read_json(path)
}

/// A trusted party's public key; the identity is refused.
pub fn read_public(path: &Path) -> Result<PublicKey, String> {
    let key: PublicKey = read_json(path)?;
    if key.public == G1::ZERO || !key.public.validate_projective() {
        return Err(format!("{}: not a public key", path.display()));
    }
    Ok(key)
}

fn powers(x: Zp, len: usize) -> Vec<Zp> {
    std::iter::successors(Some(x), |p| Some(*p * x))
        .take(len)
        .collect()
}

/// `[by_p·points_p]`, for `by` at least as long as `points`.
fn scaled<G: CurveGroupOps<Zp>>(points: &[G], by: &[Zp]) -> Vec<G> {
    points
        .par_iter()
        .zip(by)
        .map(|(g, p)| g.mul_scalar(*p))
        .collect()
}

/// `e(a, b) = e(c, d)`.
fn paired(a: G1, b: G2, c: G1, d: G2) -> bool {
    Gt::pairing(a, b) == Gt::pairing(c, d)
}

/// The CRS's points are the powers of one `α` fixed by `g_1`.
fn structured(l: &Lists, n: usize, rng: &mut dyn RngCore) -> bool {
    let (g, gh) = (&l.g_list, &l.g_hat_list);
    if n < 2 || g.len() != 2 * n || gh.len() != n || g[n] != G1::ZERO || g[0] == G1::ZERO {
        return false;
    }
    // g_{p+1} = α·g_p for every consecutive pair of powers but the gap at
    // n+1, which g_{n+2} = α²·g_n bridges; ĝ_{p+1} = α·ĝ_p.
    let pairs: Vec<usize> = (0..2 * n - 1).filter(|&i| i != n - 1 && i != n).collect();
    let r: Vec<Zp> = pairs.iter().map(|_| Zp::rand(rng)).collect();
    let next = G1::multi_mul_scalar(&pairs.iter().map(|&i| g[i + 1]).collect::<Vec<_>>(), &r);
    let this = G1::multi_mul_scalar(&pairs.iter().map(|&i| g[i]).collect::<Vec<_>>(), &r);
    let rh: Vec<Zp> = (0..n - 1).map(|_| Zp::rand(rng)).collect();
    let next_h = G2::multi_mul_scalar(&gh[1..], &rh);
    let this_h = G2::multi_mul_scalar(&gh[..n - 1], &rh);
    paired(g[0], G2::GENERATOR, G1::GENERATOR, gh[0])
        && paired(next, G2::GENERATOR, this, gh[0])
        && paired(g[n + 1], G2::GENERATOR, g[n - 1], gh[1])
        && paired(G1::GENERATOR, next_h, g[0], this_h)
}

/// Check the chain of contributions ending in the CRS `params`, and every
/// signature on it, and return their receipts.
fn check(params: &Params, t: &Transcript, rng: &mut dyn RngCore) -> Result<Vec<Receipt>, String> {
    if t.version != VERSION {
        return Err(format!("unsupported ceremony version {}", t.version));
    }
    let l = &params.g_lists;
    let valid = l.g_list.par_iter().all(G1::validate_projective)
        && l.g_hat_list.par_iter().all(G2::validate_projective)
        && t.contributions.iter().all(|c| {
            c.g1.validate_projective()
                && c.h.validate_projective()
                && c.r.validate_projective()
                && c.signature.as_ref().is_none_or(|sig| {
                    sig.signer.validate_projective() && sig.r.validate_projective()
                })
        });
    if !valid {
        return Err("a point lies outside its group".into());
    }
    let mut prev = G1::GENERATOR;
    let mut receipts = Vec::new();
    for (i, c) in t.contributions.iter().enumerate() {
        let knows = G2::GENERATOR.mul_scalar(c.s) == c.r + c.h.mul_scalar(challenge(i, prev, c));
        if c.h == G2::ZERO || !knows || !paired(c.g1, G2::GENERATOR, prev, c.h) {
            return Err(format!("contribution {i} is invalid"));
        }
        let receipt = receipt(i, prev, c);
        let signer = match &c.signature {
            Some(sig) if !signature_ok(sig, &receipt) => {
                return Err(format!("contribution {i} has an invalid signature"));
            }
            Some(sig) => Some(PublicKey { public: sig.signer }.fingerprint()),
            None => None,
        };
        receipts.push(Receipt { receipt, signer });
        prev = c.g1;
    }
    if l.g_list.first() != Some(&prev) {
        return Err("the CRS is not the result of the contributions".into());
    }
    if !structured(l, params.n, rng) {
        return Err("the CRS is not a list of powers".into());
    }
    Ok(receipts)
}

fn read(dir: &Path) -> Result<(Params, Transcript), String> {
    Ok((
        to_params(&load(&dir.join(CRS))?)?,
        read_json(&dir.join(TRANSCRIPT))?,
    ))
}

fn write(dir: &Path, params: Params, t: &Transcript) -> Result<(), String> {
    save(&from_params(params)?, &dir.join(CRS))?;
    let path = dir.join(TRANSCRIPT);
    let text = serde_json::to_string_pretty(t).map_err(|e| e.to_string())?;
    std::fs::write(&path, text).map_err(|e| format!("{}: {e}", path.display()))
}

/// Start a ceremony in `dir` from the CRS with `α = 1`: every `g_p = g`,
/// every `ĝ_p = ĝ`. Its trapdoor is public, so [`verify`] accepts it only
/// after at least one contribution.
pub fn init(dir: &Path) -> Result<(), String> {
    let mut params =
        to_params(&CompactPkeCrs::from_config(config(), CRS_MAX_BITS).map_err(|e| e.to_string())?)?;
    let n = params.n;
    let l = &mut params.g_lists;
    l.g_list = (0..2 * n)
        .map(|i| if i == n { G1::ZERO } else { G1::GENERATOR })
        .collect();
    l.g_hat_list = vec![G2::GENERATOR; n];
    let t = Transcript {
        version: VERSION.into(),
        contributions: Vec::new(),
    };
    write(dir, params, &t)
}

/// Check the ceremony in `dir`, add a contribution with a fresh secret from
/// `rng`, signed with `key` if given, and return its receipt. The secret does
/// not outlive the call.
pub fn contribute(
    dir: &Path,
    key: Option<&SecretKey>,
    rng: &mut dyn RngCore,
) -> Result<Receipt, String> {
    let (mut params, mut t) = read(dir)?;
    check(&params, &t, rng)?;
    let tau = Zp::rand(rng);
    let l = &mut params.g_lists;
    let tp = powers(tau, l.g_list.len());
    l.g_list = scaled(&l.g_list, &tp);
    l.g_hat_list = scaled(&l.g_hat_list, &tp);
    let (prev, index) = (
        t.contributions.last().map_or(G1::GENERATOR, |c| c.g1),
        t.contributions.len(),
    );
    let k = Zp::rand(rng);
    let mut c = Contribution {
        g1: l.g_list[0],
        h: G2::GENERATOR.mul_scalar(tau),
        r: G2::GENERATOR.mul_scalar(k),
        s: Zp::ZERO,
        signature: None,
    };
    c.s = k + challenge(index, prev, &c) * tau;
    let receipt = receipt(index, prev, &c);
    c.signature = key.map(|key| sign(key, &receipt, rng));
    let signer = c
        .signature
        .as_ref()
        .map(|sig| PublicKey { public: sig.signer }.fingerprint());
    t.contributions.push(c);
    write(dir, params, &t)?;
    Ok(Receipt { receipt, signer })
}

/// Check the ceremony in `dir`: at least one contribution, each valid and
/// any signature on it valid, a CRS that is their result, and, if `trusted`
/// is not empty, a contribution signed by one of `trusted`. Returns the
/// receipts in order, and the CRS that was checked, never a second read of
/// the file, which may have changed.
pub fn verify(
    dir: &Path,
    trusted: &[PublicKey],
    rng: &mut dyn RngCore,
) -> Result<(Vec<Receipt>, CompactPkeCrs), String> {
    let (params, t) = read(dir)?;
    if t.contributions.is_empty() {
        return Err("the ceremony has no contribution: its trapdoor is public".into());
    }
    let receipts = check(&params, &t, rng)?;
    let names: Vec<String> = trusted.iter().map(PublicKey::fingerprint).collect();
    if !names.is_empty()
        && !receipts
            .iter()
            .any(|r| r.signer.as_ref().is_some_and(|s| names.contains(s)))
    {
        return Err("no trusted party signed a contribution".into());
    }
    Ok((receipts, from_params(params)?))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lists(alpha: Zp, n: usize) -> Lists {
        let a = powers(alpha, 2 * n);
        Lists {
            g_list: (0..2 * n)
                .map(|i| {
                    if i == n {
                        G1::ZERO
                    } else {
                        G1::GENERATOR.mul_scalar(a[i])
                    }
                })
                .collect(),
            g_hat_list: a[..n]
                .iter()
                .map(|p| G2::GENERATOR.mul_scalar(*p))
                .collect(),
        }
    }

    #[test]
    fn powers_of_one_alpha_are_structured() {
        let rng = &mut rand::thread_rng();
        let n = 4;
        assert!(structured(&lists(Zp::rand(rng), n), n, rng));
        assert!(structured(&lists(Zp::ONE, n), n, rng));
    }

    /// Any single point off the powers is caught, the gap included.
    #[test]
    fn every_misplaced_point_is_caught() {
        let rng = &mut rand::thread_rng();
        let n = 4;
        let alpha = Zp::rand(rng);
        for i in 0..2 * n {
            let mut l = lists(alpha, n);
            l.g_list[i] += G1::GENERATOR;
            assert!(!structured(&l, n, rng), "g_{}", i + 1);
        }
        for i in 0..n {
            let mut l = lists(alpha, n);
            l.g_hat_list[i] += G2::GENERATOR;
            assert!(!structured(&l, n, rng), "ĝ_{}", i + 1);
        }
        // Two different α in G1 and G2.
        let mut l = lists(Zp::rand(rng), n);
        l.g_hat_list = lists(Zp::rand(rng), n).g_hat_list;
        assert!(!structured(&l, n, rng));
    }
}
