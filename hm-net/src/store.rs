// NOTE: File I/O in this module is synchronous because the libp2p RecordStore
// trait requires synchronous methods (get, put, remove, records). With a 1 MB
// max record size, single-file reads/writes complete in microseconds, so
// briefly blocking the async runtime is acceptable.

//! Persistent file-backed record store for Kademlia.
//!
//! Each record is stored as a file: `<data_dir>/records/<hex-key>`.
//! The keypair is persisted at `<data_dir>/keypair`.

use anyhow::{Context, Result};
use libp2p::{
    identity,
    kad::{
        store::{Error, RecordStore},
        ProviderRecord, Record, RecordKey,
    },
    PeerId,
};
use std::borrow::Cow;
use std::path::{Path, PathBuf};

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// Set file permissions to the given mode (unix only).
#[cfg(unix)]
fn set_permissions(path: &Path, mode: u32) {
    use std::os::unix::fs::PermissionsExt;
    let perms = std::fs::Permissions::from_mode(mode);
    if let Err(e) = std::fs::set_permissions(path, perms) {
        tracing::warn!("failed to set permissions on {}: {}", path.display(), e);
    }
}

/// A Kademlia record store backed by the filesystem.
pub struct FileStore {
    data_dir: PathBuf,
    local_peer_id: PeerId,
    max_records: usize,
    max_record_size: usize,
}

impl FileStore {
    pub fn new(data_dir: PathBuf, local_peer_id: PeerId) -> Result<Self> {
        let records_dir = data_dir.join("records");
        std::fs::create_dir_all(&records_dir)
            .with_context(|| format!("creating records dir: {}", records_dir.display()))?;
        Ok(Self {
            data_dir,
            local_peer_id,
            max_records: 10_000,
            max_record_size: 1_048_576, // 1 MB per record
        })
    }

    /// Override the default record limits.
    pub fn with_limits(mut self, max_records: usize, max_record_size: usize) -> Self {
        self.max_records = max_records;
        self.max_record_size = max_record_size;
        self
    }

    fn records_dir(&self) -> PathBuf {
        self.data_dir.join("records")
    }

    fn record_path(&self, key: &RecordKey) -> PathBuf {
        self.records_dir().join(hex_encode(key.as_ref()))
    }
}

impl RecordStore for FileStore {
    type RecordsIter<'a> = std::vec::IntoIter<Cow<'a, Record>>;
    type ProvidedIter<'a> = std::vec::IntoIter<Cow<'a, ProviderRecord>>;

    fn get(&self, key: &RecordKey) -> Option<Cow<'_, Record>> {
        let path = self.record_path(key);
        let value = std::fs::read(&path).ok()?;
        Some(Cow::Owned(Record {
            key: key.clone(),
            value,
            publisher: None,
            expires: None,
        }))
    }

    fn put(&mut self, record: Record) -> std::result::Result<(), Error> {
        if record.value.len() > self.max_record_size {
            return Err(Error::ValueTooLarge);
        }
        // Check record count (approximate — counts files)
        let count = std::fs::read_dir(self.records_dir())
            .map(|entries| entries.count())
            .unwrap_or(0);
        if count >= self.max_records {
            return Err(Error::MaxRecords);
        }
        let path = self.record_path(&record.key);
        std::fs::write(&path, &record.value).map_err(|_| Error::MaxRecords)?;
        Ok(())
    }

    fn remove(&mut self, key: &RecordKey) {
        let path = self.record_path(key);
        let _ = std::fs::remove_file(path);
    }

    fn records(&self) -> Self::RecordsIter<'_> {
        let dir = self.records_dir();
        let records: Vec<Cow<'_, Record>> = std::fs::read_dir(&dir)
            .into_iter()
            .flatten()
            .filter_map(|entry| {
                let entry = entry.ok()?;
                let name = entry.file_name().into_string().ok()?;
                let key_bytes = hex_decode(&name)?;
                let key = RecordKey::new(&key_bytes);
                let value = std::fs::read(entry.path()).ok()?;
                Some(Cow::Owned(Record {
                    key,
                    value,
                    publisher: None,
                    expires: None,
                }))
            })
            .collect();
        records.into_iter()
    }

    fn add_provider(&mut self, _record: ProviderRecord) -> std::result::Result<(), Error> {
        // Provider records not used for our DHT
        Ok(())
    }

    fn providers(&self, _key: &RecordKey) -> Vec<ProviderRecord> {
        Vec::new()
    }

    fn provided(&self) -> Self::ProvidedIter<'_> {
        Vec::new().into_iter()
    }

    fn remove_provider(&mut self, _key: &RecordKey, _provider: &PeerId) {}
}

fn hex_decode(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

/// Load or generate a persistent keypair.
///
/// Sets restrictive file permissions (0o600 on keypair, 0o700 on data dir) on unix.
pub fn load_or_generate_keypair(data_dir: &Path) -> Result<identity::Keypair> {
    let key_path = data_dir.join("keypair");
    if key_path.exists() {
        let bytes = std::fs::read(&key_path).context("reading keypair")?;
        // Retroactively fix permissions on existing keypair files
        #[cfg(unix)]
        set_permissions(&key_path, 0o600);
        identity::Keypair::from_protobuf_encoding(&bytes).context("decoding keypair")
    } else {
        let key = identity::Keypair::generate_ed25519();
        let bytes = key.to_protobuf_encoding().context("encoding keypair")?;
        std::fs::create_dir_all(data_dir)?;
        #[cfg(unix)]
        set_permissions(data_dir, 0o700);
        std::fs::write(&key_path, &bytes).context("writing keypair")?;
        #[cfg(unix)]
        set_permissions(&key_path, 0o600);
        Ok(key)
    }
}
