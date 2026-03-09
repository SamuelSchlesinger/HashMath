/-
  HashMath.Net.IPC — IPC protocol between Lean (hm) and Rust sidecar (hm-net)

  Wire format: [4-byte big-endian length] [tag byte] [payload]
  Communication is over stdin/stdout pipes.
-/

import HashMath.Serialize

namespace HashMath.Net

-- Request tags (Lean → Rust)
namespace ReqTag
  def ping     : UInt8 := 0x50
  def publish  : UInt8 := 0x51
  def fetch    : UInt8 := 0x52
  def getPeers : UInt8 := 0x53
  def shutdown : UInt8 := 0x54
end ReqTag

-- Response tags (Rust → Lean)
namespace RespTag
  def pong     : UInt8 := 0x60
  def published: UInt8 := 0x61
  def found    : UInt8 := 0x62
  def notFound : UInt8 := 0x63
  def peerList : UInt8 := 0x64
  def error    : UInt8 := 0x65
end RespTag

/-- A request from Lean to the Rust sidecar. -/
inductive Request where
  | ping
  | publish (hash : Hash) (declBytes : ByteArray)
  | fetch (hash : Hash)
  | getPeers
  | shutdown

/-- A response from the Rust sidecar to Lean. -/
inductive Response where
  | pong
  | published (hash : Hash)
  | found (hash : Hash) (declBytes : ByteArray)
  | notFound (hash : Hash)
  | peerList (peers : List String)
  | error (msg : String)

-- Serialization helpers

/-- Encode a Nat as 4-byte big-endian. -/
private def serU32BE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    (n / (256 * 256 * 256) % 256).toUInt8,
    (n / (256 * 256) % 256).toUInt8,
    (n / 256 % 256).toUInt8,
    (n % 256).toUInt8
  ]

/-- Decode a 4-byte big-endian Nat from a ByteArray at an offset. -/
private def desU32BE (bs : ByteArray) (off : Nat) : Option Nat :=
  if off + 4 > bs.size then none
  else
    let b0 := (bs.get! off).toNat
    let b1 := (bs.get! (off + 1)).toNat
    let b2 := (bs.get! (off + 2)).toNat
    let b3 := (bs.get! (off + 3)).toNat
    some (b0 * 256 * 256 * 256 + b1 * 256 * 256 + b2 * 256 + b3)

/-- Serialize a UTF-8 string as [LEB128 length] [bytes]. -/
private def serString (s : String) : ByteArray :=
  let bytes := s.toUTF8
  serNat bytes.size ++ bytes

/-- Serialize a request to its wire payload (tag + body, without length prefix). -/
def serializeRequest : Request → ByteArray
  | .ping => serByte ReqTag.ping
  | .publish hash declBytes =>
    serByte ReqTag.publish ++ serHash hash ++ serNat declBytes.size ++ declBytes
  | .fetch hash =>
    serByte ReqTag.fetch ++ serHash hash
  | .getPeers => serByte ReqTag.getPeers
  | .shutdown => serByte ReqTag.shutdown

/-- Serialize a response to its wire payload (tag + body, without length prefix). -/
def serializeResponse : Response → ByteArray
  | .pong => serByte RespTag.pong
  | .published hash =>
    serByte RespTag.published ++ serHash hash
  | .found hash declBytes =>
    serByte RespTag.found ++ serHash hash ++ serNat declBytes.size ++ declBytes
  | .notFound hash =>
    serByte RespTag.notFound ++ serHash hash
  | .peerList peers =>
    serByte RespTag.peerList ++ serNat peers.length ++
    ByteArray.concatList (peers.map serString)
  | .error msg =>
    serByte RespTag.error ++ serString msg

/-- Frame a payload with a 4-byte big-endian length prefix. -/
def frameMessage (payload : ByteArray) : ByteArray :=
  serU32BE payload.size ++ payload

-- Deserialization

/-- A simple cursor for reading from a ByteArray. -/
structure Cursor where
  data : ByteArray
  pos : Nat

namespace Cursor

def remaining (c : Cursor) : Nat :=
  if c.pos ≥ c.data.size then 0 else c.data.size - c.pos

def readByte (c : Cursor) : Option (UInt8 × Cursor) :=
  if c.pos < c.data.size then
    some (c.data.get! c.pos, { c with pos := c.pos + 1 })
  else none

def readBytes (c : Cursor) (n : Nat) : Option (ByteArray × Cursor) :=
  if c.pos + n ≤ c.data.size then
    some (c.data.extract c.pos (c.pos + n), { c with pos := c.pos + n })
  else none

def readHash (c : Cursor) : Option (Hash × Cursor) := do
  let (bs, c') ← c.readBytes 32
  if h : bs.size = 32 then
    some (⟨bs, h⟩, c')
  else none

def readNat (c : Cursor) : Option (Nat × Cursor) := do
  let (n, newPos) ← decodeLEB128 c.data c.pos
  some (n, { c with pos := newPos })

def readString (c : Cursor) : Option (String × Cursor) := do
  let (len, c') ← c.readNat
  let (bs, c'') ← c'.readBytes len
  some (String.fromUTF8! bs, c'')

end Cursor

private def readStrings : Cursor → Nat → List String → Option (List String × Cursor)
  | c, 0, acc => some (acc.reverse, c)
  | c, n + 1, acc => do
    let (s, c') ← c.readString
    readStrings c' n (s :: acc)

/-- Deserialize a response from a payload (after length prefix has been stripped). -/
def deserializeResponse (payload : ByteArray) : Option Response := do
  let c : Cursor := ⟨payload, 0⟩
  let (tag, c) ← c.readByte
  if tag == RespTag.pong then
    some .pong
  else if tag == RespTag.published then do
    let (hash, _) ← c.readHash
    some (.published hash)
  else if tag == RespTag.found then do
    let (hash, c) ← c.readHash
    let (len, c) ← c.readNat
    let (bs, _) ← c.readBytes len
    some (.found hash bs)
  else if tag == RespTag.notFound then do
    let (hash, _) ← c.readHash
    some (.notFound hash)
  else if tag == RespTag.peerList then do
    let (count, c) ← c.readNat
    let (peers, _) ← readStrings c count []
    some (.peerList peers)
  else if tag == RespTag.error then do
    let (msg, _) ← c.readString
    some (.error msg)
  else none

/-- Deserialize a request from a payload (for testing, and for the Rust side's reference). -/
def deserializeRequest (payload : ByteArray) : Option Request := do
  let c : Cursor := ⟨payload, 0⟩
  let (tag, c) ← c.readByte
  if tag == ReqTag.ping then
    some .ping
  else if tag == ReqTag.publish then do
    let (hash, c) ← c.readHash
    let (len, c) ← c.readNat
    let (bs, _) ← c.readBytes len
    some (.publish hash bs)
  else if tag == ReqTag.fetch then do
    let (hash, _) ← c.readHash
    some (.fetch hash)
  else if tag == ReqTag.getPeers then
    some .getPeers
  else if tag == ReqTag.shutdown then
    some .shutdown
  else none

-- IO helpers for reading/writing framed messages

/-- Read exactly n bytes from a stream. -/
private partial def readExact (stream : IO.FS.Stream) (n : Nat) : IO ByteArray := do
  let mut buf := ByteArray.empty
  while buf.size < n do
    let chunk ← stream.read (n - buf.size).toUSize
    if chunk.isEmpty then
      throw (IO.Error.userError "unexpected EOF in IPC read")
    buf := buf ++ chunk
  return buf

/-- Read a framed message from a stream: [4-byte length][payload]. -/
def recvMessage (stream : IO.FS.Stream) : IO ByteArray := do
  let lenBytes ← readExact stream 4
  match desU32BE lenBytes 0 with
  | some len => readExact stream len
  | none => throw (IO.Error.userError "invalid IPC frame length")

/-- Write a framed message to a stream. -/
def sendMessage (stream : IO.FS.Stream) (payload : ByteArray) : IO Unit := do
  stream.write (frameMessage payload)
  stream.flush

/-- Send a request over IPC. -/
def sendRequest (stream : IO.FS.Stream) (req : Request) : IO Unit :=
  sendMessage stream (serializeRequest req)

/-- Receive and deserialize a response from IPC. -/
def recvResponse (stream : IO.FS.Stream) : IO Response := do
  let payload ← recvMessage stream
  match deserializeResponse payload with
  | some resp => return resp
  | none => throw (IO.Error.userError "malformed IPC response")

/-- Send a response over IPC (used by the Rust side, included for testing). -/
def sendResponse (stream : IO.FS.Stream) (resp : Response) : IO Unit :=
  sendMessage stream (serializeResponse resp)

/-- Receive and deserialize a request from IPC. -/
def recvRequest (stream : IO.FS.Stream) : IO Request := do
  let payload ← recvMessage stream
  match deserializeRequest payload with
  | some req => return req
  | none => throw (IO.Error.userError "malformed IPC request")

end HashMath.Net
