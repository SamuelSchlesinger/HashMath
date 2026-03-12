//! IPC protocol: length-prefixed binary messages over stdin/stdout.
//!
//! Wire format: [4-byte big-endian length] [tag byte] [payload]
//! Mirrors HashMath.Net.IPC on the Lean side.

use anyhow::{bail, Context, Result};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

// Request tags (Lean → Rust)
pub mod req_tag {
    pub const PING: u8 = 0x50;
    pub const PUBLISH: u8 = 0x51;
    pub const FETCH: u8 = 0x52;
    pub const GET_PEERS: u8 = 0x53;
    pub const SHUTDOWN: u8 = 0x54;
    pub const PUBLISH_BATCH: u8 = 0x55;
}

// Response tags (Rust → Lean)
pub mod resp_tag {
    pub const PONG: u8 = 0x60;
    pub const PUBLISHED: u8 = 0x61;
    pub const FOUND: u8 = 0x62;
    pub const NOT_FOUND: u8 = 0x63;
    pub const PEER_LIST: u8 = 0x64;
    pub const ERROR: u8 = 0x65;
    pub const BATCH_PUBLISHED: u8 = 0x66;
}

/// A 32-byte SHA-256 hash, matching HashMath.Hash.
pub type Hash = [u8; 32];

/// Request from Lean to the sidecar.
#[derive(Debug, Clone)]
pub enum Request {
    Ping,
    Publish { hash: Hash, decl_bytes: Vec<u8> },
    PublishBatch { records: Vec<(Hash, Vec<u8>)> },
    Fetch { hash: Hash },
    GetPeers,
    Shutdown,
}

/// Response from the sidecar to Lean.
#[derive(Debug, Clone)]
pub enum Response {
    Pong,
    Published { hash: Hash },
    BatchPublished { count: usize },
    Found { hash: Hash, decl_bytes: Vec<u8> },
    NotFound { hash: Hash },
    PeerList { peers: Vec<String> },
    Error { msg: String },
}

// --- LEB128 codec ---

fn decode_leb128(data: &[u8], offset: usize) -> Result<(usize, usize)> {
    let mut result: usize = 0;
    let mut shift: u32 = 0;
    let mut pos = offset;
    loop {
        if pos >= data.len() {
            bail!("unexpected EOF in LEB128");
        }
        let byte = data[pos];
        result |= ((byte & 0x7F) as usize) << shift;
        pos += 1;
        if byte < 0x80 {
            return Ok((result, pos));
        }
        shift += 7;
        if shift > 63 {
            bail!("LEB128 overflow");
        }
    }
}

fn encode_leb128(mut n: usize) -> Vec<u8> {
    let mut buf = Vec::new();
    loop {
        let mut byte = (n & 0x7F) as u8;
        n >>= 7;
        if n != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if n == 0 {
            break;
        }
    }
    buf
}

// --- Cursor for reading ---

struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    fn read_byte(&mut self) -> Result<u8> {
        if self.pos >= self.data.len() {
            bail!("unexpected EOF reading byte");
        }
        let b = self.data[self.pos];
        self.pos += 1;
        Ok(b)
    }

    fn read_hash(&mut self) -> Result<Hash> {
        if self.pos + 32 > self.data.len() {
            bail!("unexpected EOF reading hash");
        }
        let mut h = [0u8; 32];
        h.copy_from_slice(&self.data[self.pos..self.pos + 32]);
        self.pos += 32;
        Ok(h)
    }

    fn read_nat(&mut self) -> Result<usize> {
        let (n, new_pos) = decode_leb128(self.data, self.pos)?;
        self.pos = new_pos;
        Ok(n)
    }

    fn read_bytes(&mut self, n: usize) -> Result<Vec<u8>> {
        if self.pos + n > self.data.len() {
            bail!("unexpected EOF reading {} bytes", n);
        }
        let bs = self.data[self.pos..self.pos + n].to_vec();
        self.pos += n;
        Ok(bs)
    }

    fn read_string(&mut self) -> Result<String> {
        let len = self.read_nat()?;
        let bs = self.read_bytes(len)?;
        String::from_utf8(bs).context("invalid UTF-8 in IPC string")
    }
}

// --- Serialization ---

fn ser_string(s: &str) -> Vec<u8> {
    let bytes = s.as_bytes();
    let mut out = encode_leb128(bytes.len());
    out.extend_from_slice(bytes);
    out
}

impl Response {
    /// Serialize a response to wire payload (tag + body, no length prefix).
    pub fn serialize(&self) -> Vec<u8> {
        match self {
            Response::Pong => vec![resp_tag::PONG],
            Response::Published { hash } => {
                let mut buf = vec![resp_tag::PUBLISHED];
                buf.extend_from_slice(hash);
                buf
            }
            Response::BatchPublished { count } => {
                let mut buf = vec![resp_tag::BATCH_PUBLISHED];
                buf.extend_from_slice(&encode_leb128(*count));
                buf
            }
            Response::Found { hash, decl_bytes } => {
                let mut buf = vec![resp_tag::FOUND];
                buf.extend_from_slice(hash);
                buf.extend_from_slice(&encode_leb128(decl_bytes.len()));
                buf.extend_from_slice(decl_bytes);
                buf
            }
            Response::NotFound { hash } => {
                let mut buf = vec![resp_tag::NOT_FOUND];
                buf.extend_from_slice(hash);
                buf
            }
            Response::PeerList { peers } => {
                let mut buf = vec![resp_tag::PEER_LIST];
                buf.extend_from_slice(&encode_leb128(peers.len()));
                for p in peers {
                    buf.extend_from_slice(&ser_string(p));
                }
                buf
            }
            Response::Error { msg } => {
                let mut buf = vec![resp_tag::ERROR];
                buf.extend_from_slice(&ser_string(msg));
                buf
            }
        }
    }
}

impl Request {
    /// Deserialize a request from wire payload (after length prefix stripped).
    pub fn deserialize(payload: &[u8]) -> Result<Self> {
        let mut c = Cursor::new(payload);
        let tag = c.read_byte()?;
        match tag {
            req_tag::PING => Ok(Request::Ping),
            req_tag::PUBLISH => {
                let hash = c.read_hash()?;
                let len = c.read_nat()?;
                let decl_bytes = c.read_bytes(len)?;
                Ok(Request::Publish { hash, decl_bytes })
            }
            req_tag::FETCH => {
                let hash = c.read_hash()?;
                Ok(Request::Fetch { hash })
            }
            req_tag::PUBLISH_BATCH => {
                let count = c.read_nat()?;
                let mut records = Vec::with_capacity(count);
                for _ in 0..count {
                    let hash = c.read_hash()?;
                    let len = c.read_nat()?;
                    let decl_bytes = c.read_bytes(len)?;
                    records.push((hash, decl_bytes));
                }
                Ok(Request::PublishBatch { records })
            }
            req_tag::GET_PEERS => Ok(Request::GetPeers),
            req_tag::SHUTDOWN => Ok(Request::Shutdown),
            _ => bail!("unknown request tag: 0x{:02x}", tag),
        }
    }
}

// --- Framed I/O ---

/// Read a framed message: [4-byte BE length][payload].
pub async fn recv_message<R: AsyncRead + Unpin>(reader: &mut R) -> Result<Vec<u8>> {
    let mut len_buf = [0u8; 4];
    reader
        .read_exact(&mut len_buf)
        .await
        .context("reading IPC frame length")?;
    let len = u32::from_be_bytes(len_buf) as usize;
    if len > 8 * 1024 * 1024 {
        bail!("IPC frame too large: {} bytes", len);
    }
    let mut payload = vec![0u8; len];
    reader
        .read_exact(&mut payload)
        .await
        .context("reading IPC frame payload")?;
    Ok(payload)
}

/// Write a framed message: [4-byte BE length][payload].
pub async fn send_message<W: AsyncWrite + Unpin>(
    writer: &mut W,
    payload: &[u8],
) -> Result<()> {
    let len = payload.len() as u32;
    writer
        .write_all(&len.to_be_bytes())
        .await
        .context("writing IPC frame length")?;
    writer
        .write_all(payload)
        .await
        .context("writing IPC frame payload")?;
    writer.flush().await.context("flushing IPC")?;
    Ok(())
}

/// Receive and deserialize a request.
pub async fn recv_request<R: AsyncRead + Unpin>(reader: &mut R) -> Result<Request> {
    let payload = recv_message(reader).await?;
    Request::deserialize(&payload)
}

/// Serialize and send a response.
pub async fn send_response<W: AsyncWrite + Unpin>(
    writer: &mut W,
    resp: &Response,
) -> Result<()> {
    send_message(writer, &resp.serialize()).await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leb128_roundtrip() {
        for n in [0, 1, 127, 128, 255, 300, 16384, 1_000_000] {
            let encoded = encode_leb128(n);
            let (decoded, _) = decode_leb128(&encoded, 0).unwrap();
            assert_eq!(n, decoded);
        }
    }

    #[test]
    fn test_request_roundtrip() {
        let hash = [42u8; 32];
        let hash2 = [99u8; 32];
        let cases = vec![
            Request::Ping,
            Request::Publish {
                hash,
                decl_bytes: vec![1, 2, 3, 4],
            },
            Request::PublishBatch {
                records: vec![(hash, vec![1, 2]), (hash2, vec![3, 4, 5])],
            },
            Request::Fetch { hash },
            Request::GetPeers,
            Request::Shutdown,
        ];
        for req in cases {
            let serialized = match &req {
                Request::Ping => vec![req_tag::PING],
                Request::Publish { hash, decl_bytes } => {
                    let mut buf = vec![req_tag::PUBLISH];
                    buf.extend_from_slice(hash);
                    buf.extend_from_slice(&encode_leb128(decl_bytes.len()));
                    buf.extend_from_slice(decl_bytes);
                    buf
                }
                Request::PublishBatch { records } => {
                    let mut buf = vec![req_tag::PUBLISH_BATCH];
                    buf.extend_from_slice(&encode_leb128(records.len()));
                    for (h, bytes) in records {
                        buf.extend_from_slice(h);
                        buf.extend_from_slice(&encode_leb128(bytes.len()));
                        buf.extend_from_slice(bytes);
                    }
                    buf
                }
                Request::Fetch { hash } => {
                    let mut buf = vec![req_tag::FETCH];
                    buf.extend_from_slice(hash);
                    buf
                }
                Request::GetPeers => vec![req_tag::GET_PEERS],
                Request::Shutdown => vec![req_tag::SHUTDOWN],
            };
            let deserialized = Request::deserialize(&serialized).unwrap();
            assert_eq!(
                std::mem::discriminant(&req),
                std::mem::discriminant(&deserialized)
            );
        }
    }
}
