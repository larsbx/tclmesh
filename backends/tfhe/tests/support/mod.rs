//! A deterministic adversarial interleaving, shared by the ceremony and
//! backend publication tests. No sleeps, polling, or production test hooks.

use rand::{rngs::StdRng, RngCore, SeedableRng};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use tclmesh_tfhe::{ceremony, CRS, LIMIT};
use tfhe::safe_serialization::safe_serialize;
use tfhe::zk::CompactPkeCrs;

pub fn crs_bytes(crs: &CompactPkeCrs) -> Vec<u8> {
    let mut bytes = Vec::new();
    safe_serialize(crs, &mut bytes, LIMIT).unwrap();
    bytes
}

pub struct CeremonyRace {
    root: PathBuf,
    pub ceremony: PathBuf,
    pub output: PathBuf,
    pub receipts: Vec<String>,
    pub verified: Vec<u8>,
    replacement: Vec<u8>,
    transcript: Vec<u8>,
}

impl CeremonyRace {
    pub fn new(name: &str) -> Self {
        static SEQUENCE: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "tclmesh-crs-race-{name}-{}-{}",
            std::process::id(),
            SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&root).unwrap();
        let ceremony = root.join("ceremony");
        let output = root.join("published");
        std::fs::create_dir(&ceremony).unwrap();
        std::fs::create_dir(&output).unwrap();
        ceremony::init(&ceremony).unwrap();
        // A correctly serialized replacement whose trapdoor is public (1).
        // It must never be adopted with the honest contributors' receipts.
        let replacement = std::fs::read(ceremony.join(CRS)).unwrap();
        let transcript = std::fs::read(ceremony.join(ceremony::TRANSCRIPT)).unwrap();
        let mut rng = StdRng::seed_from_u64(29);
        let receipts = vec![
            ceremony::contribute(&ceremony, &mut rng).unwrap(),
            ceremony::contribute(&ceremony, &mut rng).unwrap(),
        ];
        let verified = std::fs::read(ceremony.join(CRS)).unwrap();
        assert!(verified != replacement);
        Self {
            root,
            ceremony,
            output,
            receipts,
            verified,
            replacement,
            transcript,
        }
    }

    pub fn replacing_rng(&self) -> ReplaceOnRandom {
        let dir = self.ceremony.clone();
        let crs = self.replacement.clone();
        let transcript = self.transcript.clone();
        ReplaceOnRandom {
            inner: StdRng::seed_from_u64(2901),
            writer: Some(Box::new(move || {
                for (name, bytes) in [(CRS, crs), (ceremony::TRANSCRIPT, transcript)] {
                    let staged = dir.join(format!("{name}.replacement"));
                    std::fs::write(&staged, bytes).unwrap();
                    std::fs::rename(staged, dir.join(name)).unwrap();
                }
            })),
        }
    }

    pub fn assert_replaced(&self, rng: &ReplaceOnRandom) {
        rng.assert_fired();
        assert!(std::fs::read(self.ceremony.join(CRS)).unwrap() == self.replacement);
        assert_eq!(
            std::fs::read(self.ceremony.join(ceremony::TRANSCRIPT)).unwrap(),
            self.transcript
        );
    }
}

impl Drop for CeremonyRace {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

pub struct ReplaceOnRandom {
    inner: StdRng,
    writer: Option<Box<dyn FnOnce() + Send>>,
}

impl ReplaceOnRandom {
    pub fn assert_fired(&self) {
        assert!(self.writer.is_none(), "the adversarial writer must run");
    }

    fn before_random(&mut self) {
        // check() first asks for randomness in structured(), after read()
        // captured both files and the contribution chain was checked. Stop
        // there until a concurrent writer has replaced both directory entries.
        // Any later path reload therefore deterministically sees the attack.
        if let Some(writer) = self.writer.take() {
            std::thread::spawn(writer).join().unwrap();
        }
    }
}

impl RngCore for ReplaceOnRandom {
    fn next_u32(&mut self) -> u32 {
        self.before_random();
        self.inner.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.before_random();
        self.inner.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.before_random();
        self.inner.fill_bytes(dest);
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.before_random();
        self.inner.try_fill_bytes(dest)
    }
}
