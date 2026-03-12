//! Direct content transfer protocol.
//!
//! Nodes request content by hash and receive the full bytes directly,
//! bypassing the DHT for data transfer. The DHT is only used for
//! discovery (provider records), not for storing full content.
//!
//! Protocol: `/hashmath/transfer/1.0.0`
//! Request:  32-byte SHA-256 hash
//! Response: [1-byte found flag] [content bytes if found]

use async_trait::async_trait;
use libp2p::futures::prelude::*;
use libp2p::request_response::{self, Config, ProtocolSupport};
use libp2p::StreamProtocol;
use std::io;

/// Request: a 32-byte hash identifying the desired content.
#[derive(Debug, Clone)]
pub struct TransferRequest {
    pub hash: [u8; 32],
}

/// Response: either the content bytes or not-found.
#[derive(Debug, Clone)]
pub struct TransferResponse {
    pub data: Option<Vec<u8>>,
}

/// Codec for the transfer protocol.
#[derive(Debug, Clone, Default)]
pub struct TransferCodec;

#[async_trait]
impl request_response::Codec for TransferCodec {
    type Protocol = StreamProtocol;
    type Request = TransferRequest;
    type Response = TransferResponse;

    async fn read_request<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Request>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut hash = [0u8; 32];
        io.read_exact(&mut hash).await?;
        Ok(TransferRequest { hash })
    }

    async fn read_response<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Response>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut flag = [0u8; 1];
        io.read_exact(&mut flag).await?;
        if flag[0] == 0 {
            Ok(TransferResponse { data: None })
        } else {
            let mut len_buf = [0u8; 4];
            io.read_exact(&mut len_buf).await?;
            let len = u32::from_be_bytes(len_buf) as usize;
            if len > 4 * 1024 * 1024 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "transfer response too large",
                ));
            }
            let mut data = vec![0u8; len];
            io.read_exact(&mut data).await?;
            Ok(TransferResponse { data: Some(data) })
        }
    }

    async fn write_request<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
        req: Self::Request,
    ) -> io::Result<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        io.write_all(&req.hash).await?;
        io.close().await?;
        Ok(())
    }

    async fn write_response<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
        resp: Self::Response,
    ) -> io::Result<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        match resp.data {
            None => {
                io.write_all(&[0u8]).await?;
            }
            Some(data) => {
                io.write_all(&[1u8]).await?;
                io.write_all(&(data.len() as u32).to_be_bytes()).await?;
                io.write_all(&data).await?;
            }
        }
        io.close().await?;
        Ok(())
    }
}

/// Create a new transfer protocol behaviour.
pub fn new_behaviour() -> request_response::Behaviour<TransferCodec> {
    request_response::Behaviour::new(
        [(
            StreamProtocol::new("/hashmath/transfer/1.0.0"),
            ProtocolSupport::Full,
        )],
        Config::default(),
    )
}
