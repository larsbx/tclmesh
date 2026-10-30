//! `tclmesh-tfhe`: evaluates TclMesh private circuits under TFHE.
//!
//! One JSON request per line on stdin, one JSON response per line on stdout:
//!
//! ```text
//! {"op":"encrypt","type":"int","value":"120",
//!  "width":32}                                         → {"token":1,"bytes":N}
//! {"op":"evaluate","inputs":{..},"nodes":{..},
//!  "output_nodes":{..},"input_types":{..},"width":32} → {"outputs":{name:{"token":..,"bytes":..}},"trace":[ids]}
//! {"op":"decrypt","token":1}                           → {"value":"120"}
//! {"op":"destroy","token":1}                           → {}
//! {"op":"export","token":1}                            → {"keyset":K,"kind":"int32",
//!                                                         "ciphertext":base64}
//! {"op":"restore","keyset":K,"kind":..,
//!  "ciphertext":..}                                    → {"token":3,"bytes":N}
//!                                                         (refused unless K is
//!                                                         this process's keyset)
//! {"op":"publish","dir":"/path","crs":"/path",
//!  "trusted":["/key.pub"]}                             → {"receipts":[..]} (public
//!                                                         key and CRS; "crs" adopts
//!                                                         one made by
//!                                                         `tclmesh-tfhe-crs`, or
//!                                                         verifies a ceremony
//!                                                         directory, requiring a
//!                                                         contribution signed by a
//!                                                         "trusted" key if given,
//!                                                         and adopts its CRS)
//! {"op":"import","proof":"/path","context":"c",
//!  "lo":"-5","bits":8,"hi":"200","width":32}            → {"token":2,"bytes":N}
//! ```
//!
//! `publish` writes what an encrypting party needs to prove an input without
//! the client key (`tclmesh-tfhe-prove`, `src/lib.rs`). `import` verifies such
//! a proof against its context, offset, width and optional upper bound, and
//! yields `lo + a` for the proven `a < 2^bits`, or `min(lo + a, hi)`: a
//! ciphertext whose range is proved, not claimed.
//!
//! Errors are `{"error": message}`. Ciphertexts never leave the process; the
//! runtime holds opaque token numbers and each ciphertext's serialized size.
//! Every node is computed in the syntactic schedule (`spec/TclMesh/Circuit.lean`),
//! whatever the data: `select` is a homomorphic multiplexer.
//!
//! Integers are `W`-bit words, `FheInt32` or `FheInt64` ("width", fixed by
//! the profile), and wrap modulo 2^W: an overflow under encryption cannot be
//! detected. The runtime advertises results as exact only under profile
//! semantics `int<W>-checked`, which admits only circuits whose range
//! certificate proves that no intermediate leaves the word
//! (`spec/TclMesh/Range.lean`).
//!
//! Test deployment: this process holds the client key as well as the server
//! key. A production deployment keeps the client key with the data owner.
//! Keys are fresh per process unless `TCLMESH_TFHE_KEYS` names a directory,
//! where the client key (mode 0600), public key and adopted CRS persist, so
//! exported ciphertexts can be restored after a restart.

use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use tclmesh_tfhe::{
    ceremony, config, import_proven, lift, load, metadata, save, test, upper_bound_ok, Int, CRS,
    CRS_MAX_BITS, LIMIT, PROVEN_BITS, PUBLIC_KEY, WIDTHS,
};
use tfhe::prelude::*;
use tfhe::zk::CompactPkeCrs;
use tfhe::{
    set_server_key, ClientKey, CompactPublicKey, FheBool, ProvenCompactCiphertextList, ServerKey,
};

#[derive(Clone)]
enum Val {
    Int(Int),
    Bool(FheBool),
}

impl Val {
    /// This value as a `width`-bit integer: a bit is `0` or `1`; an integer
    /// of another width is refused, never converted.
    fn int(&self, width: u32) -> R<Int> {
        match self {
            Val::Int(x) if x.width() == width => Ok(x.clone()),
            Val::Int(x) => Err(format!(
                "a {}-bit integer in a {width}-bit circuit",
                x.width()
            )),
            Val::Bool(b) => Int::from_bool(width, b),
        }
    }

    fn bool(&self) -> FheBool {
        match self {
            Val::Bool(b) => b.clone(),
            Val::Int(x) => x.nonzero(),
        }
    }

    fn bytes(&self) -> usize {
        match self {
            Val::Int(x) => x.bytes(),
            Val::Bool(b) => {
                let mut buf = Vec::new();
                tfhe::safe_serialization::safe_serialize(b, &mut buf, LIMIT)
                    .expect("serialize ciphertext");
                buf.len()
            }
        }
    }
}

struct Backend {
    client: ClientKey,
    public: CompactPublicKey,
    /// Names the key pair: recovery material is restored only under it.
    keyset: String,
    /// Where the keys and CRS persist (`TCLMESH_TFHE_KEYS`), if anywhere.
    keys: Option<PathBuf>,
    crs: Option<CompactPkeCrs>,
    store: HashMap<u64, Val>,
    next: u64,
}

type R<T> = Result<T, String>;

fn text(v: &Value) -> R<String> {
    v.as_str()
        .map(String::from)
        .ok_or_else(|| format!("expected a string, got {v}"))
}

fn words(v: &Value) -> R<Vec<String>> {
    v.as_array()
        .ok_or("expected an array")?
        .iter()
        .map(text)
        .collect()
}

fn object(v: &Value) -> R<&Map<String, Value>> {
    v.as_object()
        .ok_or_else(|| "expected an object".to_string())
}

fn int(s: &str) -> R<i64> {
    s.trim().parse().map_err(|_| format!("not an integer: {s}"))
}

fn width(req: &Value) -> R<u32> {
    req["width"]
        .as_u64()
        .and_then(|w| u32::try_from(w).ok())
        .filter(|w| WIDTHS.contains(w))
        .ok_or_else(|| format!("width must be one of {WIDTHS:?}"))
}

fn refs(w: &[String]) -> Vec<String> {
    let op = w.first().map(String::as_str).unwrap_or("");
    let unary = [
        "negate",
        "not",
        "reduce-sum",
        "rotate",
        "polynomial",
        "clamp",
    ];
    let binary = [
        "add",
        "subtract",
        "multiply",
        "equal",
        "less-than",
        "less-or-equal",
        "greater-than",
        "greater-or-equal",
        "and",
        "or",
        "lookup",
    ];
    if w.len() < 2 {
        vec![]
    } else if unary.contains(&op) {
        vec![w[1].clone()]
    } else if op == "select" {
        w[1..w.len().min(4)].to_vec()
    } else if binary.contains(&op) {
        w[1..w.len().min(3)].to_vec()
    } else {
        vec![]
    }
}

/// Depth-first post-order from the outputs in sorted name order.
fn schedule(
    nodes: &BTreeMap<String, Vec<String>>,
    outputs: &BTreeMap<String, String>,
) -> Vec<String> {
    fn visit(
        id: &str,
        nodes: &BTreeMap<String, Vec<String>>,
        seen: &mut HashSet<String>,
        order: &mut Vec<String>,
    ) {
        if !seen.insert(id.to_string()) {
            return;
        }
        if let Some(w) = nodes.get(id) {
            for r in refs(w) {
                visit(&r, nodes, seen, order);
            }
        }
        order.push(id.to_string());
    }
    let (mut seen, mut order) = (HashSet::new(), Vec::new());
    for node in outputs.values() {
        visit(node, nodes, &mut seen, &mut order);
    }
    order
}

const CLIENT_KEY: &str = "client-key.bin";

/// A file only its owner can read, never written over.
fn save_private<T: serde::Serialize + tfhe::named::Named + tfhe::Versionize>(
    value: &T,
    path: &Path,
) -> R<()> {
    use std::os::unix::fs::OpenOptionsExt;
    let mut buf = Vec::new();
    tfhe::safe_serialization::safe_serialize(value, &mut buf, LIMIT).map_err(|e| e.to_string())?;
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .and_then(|mut f| f.write_all(&buf))
        .map_err(|e| format!("{}: {e}", path.display()))
}

/// The public key belongs to the client key: a random 64-bit value
/// encrypted under one decrypts under the other (a mismatched pair passes
/// with probability about 2^-64).
fn pair(client: &ClientKey, public: &CompactPublicKey) -> R<bool> {
    let x: u64 = rand::random();
    let list = tfhe::CompactCiphertextList::builder(public).push(x).build();
    let y: tfhe::FheUint64 = list
        .expand()
        .map_err(|e| e.to_string())?
        .get(0)
        .map_err(|e| e.to_string())?
        .ok_or("empty list")?;
    let y: u64 = y.decrypt(client);
    Ok(y == x)
}

/// Key material belongs to the user this process runs as: a private mode
/// on a file another user owns still lets that user read or replace it.
fn owned(path: &Path, meta: &std::fs::Metadata) -> R<()> {
    use std::os::unix::fs::MetadataExt;
    // SAFETY: geteuid has no preconditions and cannot fail.
    if meta.uid() != unsafe { libc::geteuid() } {
        return Err(format!("{}: owned by another user", path.display()));
    }
    Ok(())
}

fn hex(digest: &[u8]) -> String {
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

/// SHA3-256 of length-prefixed parts, so no two part lists collide.
fn sha3_hex(parts: &[&[u8]]) -> String {
    use sha3::{Digest, Sha3_256};
    let mut hash = Sha3_256::new();
    for part in parts {
        hash.update((part.len() as u64).to_le_bytes());
        hash.update(part);
    }
    hex(&hash.finalize())
}

fn keyset(public: &CompactPublicKey) -> R<String> {
    use sha3::{Digest, Sha3_256};
    let mut buf = Vec::new();
    tfhe::safe_serialization::safe_serialize(public, &mut buf, LIMIT).map_err(|e| e.to_string())?;
    Ok(hex(&Sha3_256::digest(&buf)))
}

const CLAIMS: &str = "claims";
const CLAIM_VERSION: &str = "tclmesh-proof-claim-v2";

/// Claim proof context `context` for `statement` under `keyset`, durably and
/// exclusively, in `dir` (`spec/TclMesh/Claims.lean`): the record is written
/// and synced under a private name, then linked into place, which fails if
/// any process sharing the directory claimed the context first, and the
/// directories holding it are synced before success. Claims are never
/// removed, so a crash after this call holds the context for good.
fn claim(dir: &Path, keyset: &str, context: &str, statement: &str) -> R<()> {
    use std::io::ErrorKind;
    use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
    let claims = dir.join(CLAIMS);
    std::fs::DirBuilder::new()
        .recursive(true)
        .mode(0o700)
        .create(&claims)
        .map_err(|e| format!("{}: {e}", claims.display()))?;
    let path = claims.join(sha3_hex(&[keyset.as_bytes(), context.as_bytes()]));
    // Contexts are caller-supplied identifiers: persist only their public digest.
    // "consumed" is irreversible even when the process never exposes a handle.
    let context_digest = sha3_hex(&[context.as_bytes()]);
    let record = json!({"version": CLAIM_VERSION, "keyset": keyset,
        "context_digest": context_digest, "statement": statement,
        "attempt": format!("{:016x}", rand::random::<u64>()), "status": "consumed"});
    let tmp = claims.join(format!(".{}.{}", std::process::id(), rand::random::<u64>()));
    let io = |e: std::io::Error| format!("{}: {e}", claims.display());
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&tmp)
        .map_err(io)?;
    file.write_all(record.to_string().as_bytes())
        .and_then(|()| file.sync_all())
        .map_err(io)?;
    let linked = std::fs::hard_link(&tmp, &path);
    let _ = std::fs::remove_file(&tmp);
    match linked {
        // The claim is durable once its entry is: sync the claims directory
        // and the key directory holding it, which may have just created it.
        Ok(()) => [claims.as_path(), dir]
            .iter()
            .try_for_each(|d| std::fs::File::open(d).and_then(|d| d.sync_all()))
            .map_err(io),
        Err(e) if e.kind() == ErrorKind::AlreadyExists => {
            let held: Value = serde_json::from_slice(&std::fs::read(&path).map_err(io)?)
                .map_err(|e| format!("{}: {e}", path.display()))?;
            Err(
                if held["version"] != CLAIM_VERSION || held["status"] != "consumed" {
                    format!("context claimed: {context} has an unrecognized claim record; HOLD")
                } else if held["keyset"] != keyset || held["context_digest"] != context_digest {
                    format!(
                        "context claimed: {} holds a claim of another keyset or context",
                        path.display()
                    )
                } else if held["statement"] != statement {
                    format!("context claimed: {context} was claimed for another statement")
                } else {
                    format!("context claimed: {context} (attempt {})", held["attempt"])
                },
            )
        }
        Err(e) => Err(io(e)),
    }
}

impl Backend {
    /// Fresh keys for this process only.
    #[cfg(test)]
    fn new() -> Self {
        Self::open(None).expect("fresh keys")
    }

    /// The keys in `keys`, made there on first use, or fresh ones that die
    /// with the process. The server key is derived from the client key.
    fn open(keys: Option<&Path>) -> R<Self> {
        let (public, crs, client) = match keys {
            None => {
                let client = ClientKey::generate(config());
                (CompactPublicKey::new(&client), None, client)
            }
            Some(dir) => {
                // Newly created persistent key directories are private.  Do
                // not silently trust an existing world- or group-accessible
                // directory (including one reached through a symlink).
                use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
                std::fs::DirBuilder::new()
                    .recursive(true)
                    .mode(0o700)
                    .create(dir)
                    .map_err(|e| format!("{}: {e}", dir.display()))?;
                let dir_meta = std::fs::symlink_metadata(dir)
                    .map_err(|e| format!("{}: {e}", dir.display()))?;
                if !dir_meta.is_dir() || dir_meta.permissions().mode() & 0o077 != 0 {
                    return Err(format!(
                        "{}: persistent key directory must be a private, non-symlink directory (mode 0700)",
                        dir.display()
                    ));
                }
                owned(dir, &dir_meta)?;
                let path = dir.join(CLIENT_KEY);
                // A public key without its client key names a keyset whose
                // secret is gone: a fresh client key must not take its name.
                if !path.exists() && dir.join(PUBLIC_KEY).exists() {
                    return Err(format!(
                        "{}: a public key without its client key",
                        dir.display()
                    ));
                }
                let client: ClientKey = if path.exists() {
                    // The default loader follows links and does not validate
                    // permissions.  Existing/backup-restored secrets must meet
                    // the same security boundary as newly generated ones.
                    let meta = std::fs::symlink_metadata(&path)
                        .map_err(|e| format!("{}: {e}", path.display()))?;
                    if !meta.is_file() || meta.permissions().mode() & 0o777 != 0o600 {
                        return Err(format!(
                            "{}: persistent client key must be a regular, non-symlink file with mode 0600",
                            path.display()
                        ));
                    }
                    owned(&path, &meta)?;
                    load(&path)?
                } else {
                    let client = ClientKey::generate(config());
                    save_private(&client, &path)?;
                    client
                };
                let path = dir.join(PUBLIC_KEY);
                let public: CompactPublicKey = if path.exists() {
                    load(&path)?
                } else {
                    let public = CompactPublicKey::new(&client);
                    save(&public, &path)?;
                    public
                };
                let path = dir.join(CRS);
                let crs = if path.exists() {
                    Some(load(&path)?)
                } else {
                    None
                };
                (public, crs, client)
            }
        };
        set_server_key(ServerKey::new(&client));
        if keys.is_some() && !pair(&client, &public)? {
            return Err("the public key does not belong to the client key".into());
        }
        Ok(Backend {
            keyset: keyset(&public)?,
            keys: keys.map(Path::to_path_buf),
            public,
            crs,
            client,
            store: HashMap::new(),
            next: 0,
        })
    }

    /// Keep the CRS with the keys, so it stays fixed across restarts. The
    /// file is created atomically: when another process sharing the keys
    /// fixed one first, its CRS wins, and an `adopted` CRS that differs
    /// from it is refused.
    fn persist_crs(&mut self, adopted: bool) -> R<()> {
        let (Some(dir), Some(crs)) = (&self.keys, &self.crs) else {
            return Ok(());
        };
        let (path, tmp) = (
            dir.join(CRS),
            dir.join(format!(".{CRS}.{}", std::process::id())),
        );
        save(crs, &tmp)?;
        let linked = std::fs::hard_link(&tmp, &path);
        let ours = std::fs::read(&tmp).map_err(|e| format!("{}: {e}", tmp.display()));
        let _ = std::fs::remove_file(&tmp);
        match linked {
            Ok(()) => Ok(()),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                let theirs =
                    std::fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?;
                if theirs == ours? {
                    return Ok(());
                }
                self.crs = Some(load(&path)?);
                if adopted {
                    Err("another CRS is already fixed for these keys".into())
                } else {
                    Ok(())
                }
            }
            Err(e) => Err(format!("{}: {e}", path.display())),
        }
    }

    /// A ciphertext as recovery material bound to this keyset.
    fn export(&self, req: &Value) -> R<Value> {
        let mut buf = Vec::new();
        let kind = match self.token(&req["token"])? {
            Val::Int(Int::W32(x)) => {
                tfhe::safe_serialization::safe_serialize(x, &mut buf, LIMIT).map(|_| "int32")
            }
            Val::Int(Int::W64(x)) => {
                tfhe::safe_serialization::safe_serialize(x, &mut buf, LIMIT).map(|_| "int64")
            }
            Val::Bool(b) => {
                tfhe::safe_serialization::safe_serialize(b, &mut buf, LIMIT).map(|_| "bool")
            }
        }
        .map_err(|e| e.to_string())?;
        use base64::Engine;
        Ok(json!({"keyset": self.keyset, "kind": kind,
            "ciphertext": base64::engine::general_purpose::STANDARD.encode(buf)}))
    }

    /// The ciphertext in recovery material from [`Backend::export`], refused
    /// unless it was made under this keyset.
    fn restore(&mut self, req: &Value) -> R<Value> {
        if text(&req["keyset"])? != self.keyset {
            return Err("recovery material belongs to another keyset".into());
        }
        use base64::Engine;
        let bytes = base64::engine::general_purpose::STANDARD
            .decode(text(&req["ciphertext"])?)
            .map_err(|e| e.to_string())?;
        fn read<T: serde::de::DeserializeOwned + tfhe::named::Named + tfhe::Unversionize>(
            bytes: &[u8],
        ) -> R<T> {
            tfhe::safe_serialization::safe_deserialize(bytes, LIMIT).map_err(|e| e.to_string())
        }
        let v = match text(&req["kind"])?.as_str() {
            "int32" => Val::Int(Int::W32(read(&bytes)?)),
            "int64" => Val::Int(Int::W64(read(&bytes)?)),
            "bool" => Val::Bool(read(&bytes)?),
            other => return Err(format!("unknown ciphertext kind: {other}")),
        };
        Ok(self.keep(v))
    }

    fn keep(&mut self, v: Val) -> Value {
        self.next += 1;
        let bytes = v.bytes();
        self.store.insert(self.next, v);
        json!({"token": self.next, "bytes": bytes})
    }

    fn fresh(&self, ty: &str, value: &str, width: u32) -> R<Val> {
        Ok(match ty {
            "bool" => Val::Bool(FheBool::encrypt(int(value)? != 0, &self.client)),
            "int" => Val::Int(Int::encrypt(width, int(value)?, &self.client)?),
            other => return Err(format!("unsupported type: {other}")),
        })
    }

    fn trivial(ty: &str, value: &str, width: u32) -> R<Val> {
        Ok(match ty {
            "bool" => Val::Bool(FheBool::encrypt_trivial(int(value)? != 0)),
            _ => Val::Int(Int::trivial(width, int(value)?)?),
        })
    }

    fn token(&self, v: &Value) -> R<&Val> {
        let id = v.as_u64().ok_or("token must be a number")?;
        self.store
            .get(&id)
            .ok_or_else(|| format!("unknown token {id}"))
    }

    fn evaluate(&mut self, req: &Value) -> R<Value> {
        let nodes: BTreeMap<String, Vec<String>> = object(&req["nodes"])?
            .iter()
            .map(|(k, v)| Ok((k.clone(), words(v)?)))
            .collect::<R<_>>()?;
        let outputs: BTreeMap<String, String> = object(&req["output_nodes"])?
            .iter()
            .map(|(k, v)| Ok((k.clone(), text(v)?)))
            .collect::<R<_>>()?;
        let types = object(&req["input_types"])?;
        let w = width(req)?;
        let inputs = object(&req["inputs"])?;
        let order = schedule(&nodes, &outputs);
        let mut vals: HashMap<String, Val> = HashMap::new();
        for id in &order {
            let node = nodes.get(id).ok_or_else(|| format!("unknown node {id}"))?;
            let arg = |i: usize| -> R<Val> {
                let r = node
                    .get(i)
                    .ok_or_else(|| format!("node {id}: missing operand"))?;
                vals.get(r)
                    .cloned()
                    .ok_or_else(|| format!("node {id}: operand {r} not computed"))
            };
            let int = |i: usize| arg(i)?.int(w);
            let v = match node[0].as_str() {
                "input" => {
                    let name = &node[1];
                    let input = inputs
                        .get(name)
                        .ok_or_else(|| format!("missing input {name}"))?;
                    let ty = text(types.get(name).ok_or("missing input type")?)?;
                    if let Some(t) = input.get("cipher") {
                        // Identity outputs and Boolean consumers need not
                        // pass through Val::int, so check width at ingress.
                        match self.token(t)? {
                            Val::Int(x) if x.width() != w => {
                                return Err(format!(
                                    "a {}-bit integer in a {w}-bit circuit",
                                    x.width()
                                ));
                            }
                            value => value.clone(),
                        }
                    } else {
                        Self::trivial(&ty, &text(&input["public"])?, w)?
                    }
                }
                "constant" => Self::trivial("int", &node[1], w)?,
                "add" => Val::Int(lift!(|a, b| a + b, int(1)?, int(2)?)?),
                "subtract" => Val::Int(lift!(|a, b| a - b, int(1)?, int(2)?)?),
                "multiply" => Val::Int(lift!(|a, b| a * b, int(1)?, int(2)?)?),
                "negate" => Val::Int(lift!(|a| -a, int(1)?)),
                "equal" => Val::Bool(test!(|a, b| a.eq(b), int(1)?, int(2)?)?),
                "less-than" => Val::Bool(test!(|a, b| a.lt(b), int(1)?, int(2)?)?),
                "less-or-equal" => Val::Bool(test!(|a, b| a.le(b), int(1)?, int(2)?)?),
                "greater-than" => Val::Bool(test!(|a, b| a.gt(b), int(1)?, int(2)?)?),
                "greater-or-equal" => Val::Bool(test!(|a, b| a.ge(b), int(1)?, int(2)?)?),
                "and" => Val::Bool(arg(1)?.bool() & arg(2)?.bool()),
                "or" => Val::Bool(arg(1)?.bool() | arg(2)?.bool()),
                "not" => Val::Bool(!arg(1)?.bool()),
                // max/min never overflow: the declared range holds whatever
                // the ciphertext held (`spec/TclMesh/Range.lean`, `guarded_sound`).
                "clamp" => {
                    let bound = |i: usize| -> R<Int> {
                        let b = node
                            .get(i)
                            .ok_or_else(|| format!("node {id}: missing bound"))?;
                        Int::trivial(w, crate::int(b)?)
                    };
                    let x = lift!(|x, lo| x.max(&lo), int(1)?, bound(2)?)?;
                    Val::Int(lift!(|x, hi| x.min(&hi), x, bound(3)?)?)
                }
                "select" => {
                    let c = arg(1)?.bool();
                    match (arg(2)?, arg(3)?) {
                        (Val::Bool(a), Val::Bool(b)) => Val::Bool((&c & &a) | (!&c & &b)),
                        (a, b) => Val::Int(lift!(|a, b| c.select(&a, &b), a.int(w)?, b.int(w)?)?),
                    }
                }
                other => return Err(format!("unsupported operation under TFHE: {other}")),
            };
            vals.insert(id.clone(), v);
        }
        let mut out = Map::new();
        for (name, node) in &outputs {
            let v = vals.get(node).cloned().ok_or("output not computed")?;
            out.insert(name.clone(), self.keep(v));
        }
        Ok(json!({"outputs": out, "trace": order}))
    }

    /// The CRS: adopted from `publish` (generated by another party with
    /// `tclmesh-tfhe-crs`, or by a verified ceremony), or else generated here on first use, in which case
    /// this process, which holds the client key, also knows its trapdoor.
    fn crs(&mut self) -> R<&CompactPkeCrs> {
        if self.crs.is_none() {
            self.crs = Some(
                CompactPkeCrs::from_config(config(), CRS_MAX_BITS).map_err(|e| e.to_string())?,
            );
            self.persist_crs(false)?;
        }
        Ok(self.crs.as_ref().expect("generated above"))
    }

    fn publish(&mut self, req: &Value) -> R<Value> {
        self.publish_with_rng(req, &mut rand::rngs::OsRng)
    }

    fn publish_with_rng(&mut self, req: &Value, rng: &mut dyn rand::RngCore) -> R<Value> {
        let dir = text(&req["dir"])?;
        let dir = Path::new(&dir);
        let mut receipts = Vec::new();
        let trusted = match req.get("trusted") {
            Some(t) => words(t)?
                .iter()
                .map(|p| ceremony::read_public(Path::new(p)))
                .collect::<R<Vec<_>>>()?,
            None => Vec::new(),
        };
        if let Some(path) = req.get("crs") {
            if self.crs.is_some() {
                return Err("the CRS is already fixed for this process".into());
            }
            let path = text(path)?;
            let path = Path::new(&path);
            self.crs = Some(if path.is_dir() {
                let (rs, crs) = ceremony::verify(path, &trusted, rng)?;
                receipts = rs;
                crs
            } else if trusted.is_empty() {
                load(path)?
            } else {
                return Err("trusted contributors need a ceremony directory".into());
            });
            self.persist_crs(true)?;
        } else if !trusted.is_empty() {
            return Err("trusted contributors need a ceremony directory".into());
        }
        save(&self.public, &dir.join(PUBLIC_KEY))?;
        save(self.crs()?, &dir.join(CRS))?;
        Ok(json!({"receipts": receipts}))
    }

    /// Verify a proven `bits`-bit offset bound to (context, lo, bits) and
    /// return `lo + a` as a `width`-bit word; `[lo, lo + 2^bits - 1]` must
    /// lie in the word.
    fn import(&mut self, req: &Value) -> R<Value> {
        let bits = req["bits"].as_u64().ok_or("bits must be a number")? as usize;
        if !PROVEN_BITS.contains(&bits) {
            return Err(format!("bits must be one of {PROVEN_BITS:?}"));
        }
        let w = width(req)?;
        let lo = int(&text(&req["lo"])?)?;
        let hi = match req.get("hi") {
            Some(h) => {
                let h = int(&text(h)?)?;
                if !upper_bound_ok(lo, bits, h) {
                    return Err("hi must lie in [lo, lo + 2^bits - 1]".into());
                }
                Some(h)
            }
            None => None,
        };
        let list: ProvenCompactCiphertextList = load(Path::new(&text(&req["proof"])?))?;
        let context = text(&req["context"])?;
        let public = self.public.clone();
        let x = import_proven(&list, self.crs()?, &public, &context, w, lo, bits, hi)?;
        // Commit before expose: with persistent keys, the context is claimed
        // for this keyset, across processes and stores, before any handle
        // to the input exists. Only verified proofs reach the claim.
        if let Some(dir) = &self.keys {
            let statement = sha3_hex(&[&metadata(&context, lo, bits, hi), &w.to_le_bytes()]);
            claim(dir, &self.keyset, &context, &statement)?;
        }
        Ok(self.keep(Val::Int(x)))
    }

    fn handle(&mut self, req: &Value) -> R<Value> {
        match req["op"].as_str().unwrap_or("") {
            "encrypt" => {
                let ty = text(&req["type"])?;
                let w = if ty == "int" { width(req)? } else { 32 };
                let v = self.fresh(&ty, &text(&req["value"])?, w)?;
                Ok(self.keep(v))
            }
            "evaluate" => self.evaluate(req),
            "publish" => self.publish(req),
            "import" => self.import(req),
            "decrypt" => Ok(match self.token(&req["token"])? {
                Val::Int(x) => json!({"value": x.decrypt(&self.client).to_string()}),
                Val::Bool(b) => {
                    let v: bool = b.decrypt(&self.client);
                    json!({"value": if v { "1" } else { "0" }})
                }
            }),
            "export" => self.export(req),
            "restore" => self.restore(req),
            "keyset" => Ok(json!({"keyset": self.keyset})),
            "destroy" => {
                let id = req["token"].as_u64().ok_or("token must be a number")?;
                self.store.remove(&id);
                Ok(json!({}))
            }
            other => Err(format!("unknown operation: {other}")),
        }
    }
}

fn main() {
    let keys = std::env::var_os("TCLMESH_TFHE_KEYS").map(PathBuf::from);
    let mut backend = Backend::open(keys.as_deref()).unwrap_or_else(|e| {
        eprintln!("tclmesh-tfhe: {e}");
        std::process::exit(1);
    });
    let stdout = std::io::stdout();
    for line in std::io::stdin().lock().lines() {
        let Ok(line) = line else { break };
        if line.trim().is_empty() {
            continue;
        }
        let response = serde_json::from_str::<Value>(&line)
            .map_err(|e| e.to_string())
            .and_then(|req| backend.handle(&req))
            .unwrap_or_else(|e| json!({"error": e}));
        let mut out = stdout.lock();
        writeln!(out, "{response}").expect("write response");
        out.flush().expect("flush response");
    }
}

#[cfg(test)]
#[path = "../tests/support/mod.rs"]
mod test_support;

#[cfg(test)]
mod tests {
    use super::*;
    use test_support::{crs_bytes, CeremonyRace};

    fn keydir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("tclmesh-keys-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    /// A key directory missing its client key, or holding another pair's
    /// public key, is refused rather than given fresh secrets under an old
    /// keyset's name.
    #[test]
    fn incomplete_or_mismatched_key_directories_are_refused() {
        let (a, b) = (keydir("a"), keydir("b"));
        let first = Backend::open(Some(&a)).unwrap().keyset;
        assert_eq!(Backend::open(Some(&a)).unwrap().keyset, first);
        Backend::open(Some(&b)).unwrap();
        std::fs::copy(b.join(PUBLIC_KEY), a.join(PUBLIC_KEY)).unwrap();
        let err = Backend::open(Some(&a)).err().unwrap();
        assert!(err.contains("does not belong"), "{err}");
        std::fs::remove_file(b.join(CLIENT_KEY)).unwrap();
        let err = Backend::open(Some(&b)).err().unwrap();
        assert!(err.contains("without its client key"), "{err}");
        for d in [a, b] {
            std::fs::remove_dir_all(d).unwrap();
        }
    }

    /// Existing key material must not bypass the creation-time security
    /// invariants after a backup restore, chmod, or symlink substitution.
    #[test]
    fn insecure_existing_key_material_is_refused() {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let dir = keydir("permissions");
        Backend::open(Some(&dir)).unwrap();
        let key = dir.join(CLIENT_KEY);
        std::fs::set_permissions(&key, std::fs::Permissions::from_mode(0o644)).unwrap();
        let error = Backend::open(Some(&dir)).err().unwrap();
        assert!(error.contains("mode 0600"), "{error}");
        std::fs::set_permissions(&key, std::fs::Permissions::from_mode(0o600)).unwrap();

        let original = dir.join("client-key-original.bin");
        std::fs::rename(&key, &original).unwrap();
        symlink(&original, &key).unwrap();
        let error = Backend::open(Some(&dir)).err().unwrap();
        assert!(error.contains("non-symlink"), "{error}");
        std::fs::remove_file(&key).unwrap();
        std::fs::rename(&original, &key).unwrap();

        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o755)).unwrap();
        let error = Backend::open(Some(&dir)).err().unwrap();
        assert!(error.contains("private, non-symlink"), "{error}");
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        assert!(Backend::open(Some(&dir)).is_ok());

        // Another user's key: only root can hand a file to another user, so
        // the case is exercised where the tests run as root.
        // SAFETY: geteuid has no preconditions and cannot fail.
        if unsafe { libc::geteuid() } == 0 {
            std::os::unix::fs::chown(&key, Some(65534), None).unwrap();
            let error = Backend::open(Some(&dir)).err().unwrap();
            assert!(error.contains("owned by another user"), "{error}");
        }
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// Backends sharing a key directory fix one CRS: the first to persist
    /// wins, a later lazily generated one yields to it, and adopting a
    /// different one is refused.
    #[test]
    fn backends_sharing_keys_fix_one_crs() {
        let dir = keydir("shared");
        Backend::open(Some(&dir)).unwrap();
        let (mut first, mut second, mut third) = (
            Backend::open(Some(&dir)).unwrap(),
            Backend::open(Some(&dir)).unwrap(),
            Backend::open(Some(&dir)).unwrap(),
        );
        let fixed = crs_bytes(first.crs().unwrap());
        assert!(crs_bytes(second.crs().unwrap()) == fixed);
        let other = dir.join("other-crs.bin");
        save(
            &CompactPkeCrs::from_config(config(), CRS_MAX_BITS).unwrap(),
            &other,
        )
        .unwrap();
        let out = dir.join("published");
        std::fs::create_dir_all(&out).unwrap();
        let err = third
            .publish(&json!({"dir": out, "crs": other}))
            .unwrap_err();
        assert!(err.contains("already fixed"), "{err}");
        assert!(crs_bytes(third.crs.as_ref().unwrap()) == fixed);
        assert!(std::fs::read(dir.join(CRS)).unwrap() == fixed);
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// Claims are exclusive under real concurrency: of many threads claiming
    /// one context at once, exactly one succeeds; the rest learn why.
    #[test]
    fn concurrent_claims_admit_exactly_one() {
        let dir = keydir("claims-race");
        std::fs::create_dir_all(&dir).unwrap();
        let wins: Vec<bool> = std::thread::scope(|s| {
            (0..16)
                .map(|_| s.spawn(|| claim(&dir, "K", "ctx/race", "S").is_ok()))
                .collect::<Vec<_>>()
                .into_iter()
                .map(|t| t.join().unwrap())
                .collect()
        });
        assert_eq!(wins.iter().filter(|w| **w).count(), 1);
        let err = claim(&dir, "K", "ctx/race", "S").unwrap_err();
        assert!(
            err.starts_with("context claimed: ctx/race (attempt"),
            "{err}"
        );
        // Another statement under the same context is refused as such; a
        // claim file whose record names another context is refused too.
        let err = claim(&dir, "K", "ctx/race", "other").unwrap_err();
        assert!(err.contains("another statement"), "{err}");
        assert!(claim(&dir, "K2", "ctx/race", "S").is_ok());
        let claims = dir.join(CLAIMS);
        let forged = claims.join(sha3_hex(&[b"K", b"ctx/forged"]));
        std::fs::copy(claims.join(sha3_hex(&[b"K", b"ctx/race"])), &forged).unwrap();
        let err = claim(&dir, "K", "ctx/forged", "S").unwrap_err();
        assert!(err.contains("another keyset or context"), "{err}");
        // Invalid or incomplete authority records can never authorize a retry.
        let original = std::fs::read(&forged).unwrap();
        for field in ["version", "status"] {
            let mut record: Value = serde_json::from_slice(&original).unwrap();
            record[field] = json!("unknown");
            std::fs::write(&forged, record.to_string()).unwrap();
            let err = claim(&dir, "K", "ctx/forged", "S").unwrap_err();
            assert!(err.contains("HOLD"), "{err}");
        }
        // No temporary files are left behind.
        let names: Vec<_> = std::fs::read_dir(&claims)
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .collect();
        assert!(
            names.iter().all(|n| !n.to_string_lossy().starts_with('.')),
            "{names:?}"
        );
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// Commit before expose, and fail closed: a backend that claimed a
    /// context and then died before any handle persisted holds the context
    /// for every later backend on the same keys; a new context still imports.
    #[test]
    fn a_claim_outlives_its_importer() {
        let dir = keydir("claim-crash");
        let prove = |b: &mut Backend, context: &str| {
            let path = dir.join(format!("{}.proof", context.replace('/', "-")));
            let list = ProvenCompactCiphertextList::builder(&b.public)
                .push_with_num_bits(7u32, 8)
                .unwrap()
                .build_with_proof_packed(
                    b.crs().unwrap(),
                    &metadata(context, 0, 8, None),
                    tfhe::zk::ZkComputeLoad::Proof,
                )
                .unwrap();
            save(&list, &path).unwrap();
            json!({"op": "import", "proof": path, "context": context, "lo": "0", "bits": 8,
                "width": 32})
        };
        let mut first = Backend::open(Some(&dir)).unwrap();
        let req = prove(&mut first, "ctx/1");
        assert!(first.handle(&req).is_ok());
        drop(first);
        let mut second = Backend::open(Some(&dir)).unwrap();
        let req = prove(&mut second, "ctx/1");
        let err = second.handle(&req).unwrap_err();
        assert!(err.starts_with("context claimed: ctx/1"), "{err}");
        let req = prove(&mut second, "ctx/2");
        let token = second.handle(&req).unwrap()["token"].clone();
        let value = second
            .handle(&json!({"op": "decrypt", "token": token}))
            .unwrap();
        assert_eq!(value["value"], "7");
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// Recovery material restores the same ciphertext under its keyset and
    /// is refused under any other.
    #[test]
    fn recovery_material_is_bound_to_its_keyset() {
        let mut backend = Backend::new();
        let mut tokens = Vec::new();
        for (ty, value, width) in [
            ("int", "-7", 32),
            ("int", "5000000000", 64),
            ("bool", "1", 32),
        ] {
            let v = backend.fresh(ty, value, width).unwrap();
            tokens.push((backend.keep(v)["token"].clone(), value));
        }
        for (token, value) in tokens {
            let mut material = backend.export(&json!({"token": token})).unwrap();
            let restored = backend.restore(&material).unwrap();
            let got = backend
                .handle(&json!({"op": "decrypt", "token": restored["token"]}))
                .unwrap();
            assert_eq!(got["value"], value);
            material["keyset"] = json!("0".repeat(64));
            assert!(backend
                .restore(&material)
                .unwrap_err()
                .contains("another keyset"));
        }
    }

    #[test]
    fn publish_uses_verified_snapshot_when_ceremony_files_are_replaced() {
        let race = CeremonyRace::new("publish");
        let mut backend = Backend::new();
        let mut rng = race.replacing_rng();
        let response = backend
            .publish_with_rng(&json!({"dir": race.output, "crs": race.ceremony}), &mut rng)
            .unwrap();

        race.assert_replaced(&rng);
        assert_eq!(response["receipts"], json!(race.receipts));
        assert!(
            crs_bytes(backend.crs.as_ref().unwrap()) == race.verified,
            "CRS differs from verified snapshot"
        );
        assert!(std::fs::read(race.output.join(CRS)).unwrap() == race.verified);
        let public: CompactPublicKey = load(&race.output.join(PUBLIC_KEY)).unwrap();
        assert_eq!(public, backend.public);

        // Later publication also uses the fixed in-memory object, despite
        // the ceremony directory now containing the public-trapdoor CRS.
        assert_eq!(
            backend.publish(&json!({"dir": race.output})).unwrap(),
            json!({"receipts": []})
        );
        assert!(std::fs::read(race.output.join(CRS)).unwrap() == race.verified);
        assert!(backend
            .publish(&json!({"dir": race.output, "crs": race.ceremony}))
            .unwrap_err()
            .contains("already fixed"));
    }
}
