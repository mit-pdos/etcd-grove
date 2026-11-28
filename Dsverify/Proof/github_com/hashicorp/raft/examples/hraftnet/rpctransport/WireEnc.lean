/-
The wire values of the hraft kit transport's RPCs (`rpctransport`'s wire structs) as pure records,
and their encodings by the kit's generated codec (`examples/hraftnet/rpc_gen.go`, by
`models/net/rpc/rpcgen.py`) as pure functions of the records.

A top-level value is its type's name (`rpcPutTag`: the name's length, 8 bytes little-endian, and
its bytes) and the value. A string is its length and its bytes; a `uint64` (and an `int64`, a
`raft.ProtocolVersion`, a `raft.SnapshotVersion`, a `raft.LogType`) 8 bytes little-endian; a `bool`
one byte; a byte slice its count and each byte as a `uint64`; a slice of structs its count and its
elements. A struct is the byte 1, then per field a byte 1 and the field's value if the field is
sent (not its zero value: gob's rule; a struct field is always sent), else a byte 0.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Wire
public import Perennial.Std.Word.LittleEndian

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-! ## The encodings -/

/-- A `uint64`. -/
def encU64 (x : w64) : List w8 := u64Le x

/-- A string: its length and its bytes. -/
def encStr (s : List w8) : List w8 := u64Le (W64 s.length) ++ s

/-- A byte slice: its count and each byte as a `uint64`. -/
def encBytes (s : List w8) : List w8 :=
  u64Le (W64 s.length) ++ (s.map fun b => u64Le (W64 (uint.Z b))).flatten

/-- A `bool`. -/
def encBool (b : Bool) : List w8 := [if b then W8 1 else W8 0]

/-- A struct field: sent (`1` and its value) or not (`0`). -/
def fld (sent : Bool) (body : List w8) : List w8 := if sent then W8 1 :: body else [W8 0]

def fStr (s : List w8) : List w8 := fld (decide (s ≠ [])) (encStr s)
def fBytes (s : List w8) : List w8 := fld (decide (s ≠ [])) (encBytes s)
def fU64 (x : w64) : List w8 := fld (decide (x ≠ W64 0)) (encU64 x)
def fU8 (x : w8) : List w8 := fld (decide (x ≠ W8 0)) (encU64 (W64 (uint.Z x)))
def fBool (b : Bool) : List w8 := fld b (encBool b)

/-- A struct of the fields `fs`. -/
def strct (fs : List (List w8)) : List w8 := W8 1 :: fs.flatten

/-- A struct-valued field (always sent). -/
def fStruct (body : List w8) : List w8 := fld true body

/-- A top-level value of the type named `t`. -/
def tagged (t : List w8) (body : List w8) : List w8 := encStr t ++ body

/-! ## The wire values -/

/-- A `Header`. -/
structure HdrV where
  pv : w64
  id : List w8
  addr : List w8

def encHdr (h : HdrV) : List w8 := strct [fU64 h.pv, fBytes h.id, fBytes h.addr]

def encEnt (e : EntV) : List w8 :=
  strct [fU64 e.index, fU64 e.term, fU8 e.ty, fBytes e.data, fBytes e.ext]

/-- A `[]Entry` field. -/
def fEnts (es : List EntV) : List w8 :=
  fld (decide (es ≠ [])) (encU64 (W64 es.length) ++ (es.map encEnt).flatten)

/-- An `AppendReq`. -/
structure AEReqV where
  hdr : HdrV
  term : w64
  leader : List w8
  prev : w64
  prevTerm : w64
  ents : List EntV
  lci : w64

def encAEReq (v : AEReqV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.AppendReq"
    (strct [fStruct (encHdr v.hdr), fU64 v.term, fBytes v.leader, fU64 v.prev, fU64 v.prevTerm,
      fEnts v.ents, fU64 v.lci])

/-- An `AppendResp`. -/
structure AERespV where
  failed : Bool
  err : List w8
  hdr : HdrV
  term : w64
  lastLog : w64
  success : Bool
  noRetry : Bool

def encAEResp (v : AERespV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.AppendResp"
    (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fU64 v.lastLog,
      fBool v.success, fBool v.noRetry])

/-- A `VoteReq`. -/
structure VoteReqV where
  hdr : HdrV
  term : w64
  cand : List w8
  lastIdx : w64
  lastTerm : w64
  transfer : Bool

def encVoteReq (v : VoteReqV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.VoteReq"
    (strct [fStruct (encHdr v.hdr), fU64 v.term, fBytes v.cand, fU64 v.lastIdx, fU64 v.lastTerm,
      fBool v.transfer])

/-- A `VoteResp`. -/
structure VoteRespV where
  failed : Bool
  err : List w8
  hdr : HdrV
  term : w64
  peers : List w8
  granted : Bool

def encVoteResp (v : VoteRespV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.VoteResp"
    (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBytes v.peers,
      fBool v.granted])

/-- A `PreVoteReq`. -/
structure PreVoteReqV where
  hdr : HdrV
  term : w64
  lastIdx : w64
  lastTerm : w64

def encPreVoteReq (v : PreVoteReqV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.PreVoteReq"
    (strct [fStruct (encHdr v.hdr), fU64 v.term, fU64 v.lastIdx, fU64 v.lastTerm])

/-- A `PreVoteResp`. -/
structure PreVoteRespV where
  failed : Bool
  err : List w8
  hdr : HdrV
  term : w64
  granted : Bool

def encPreVoteResp (v : PreVoteRespV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.PreVoteResp"
    (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBool v.granted])

/-- A `SnapReq`. -/
structure SnapReqV where
  hdr : HdrV
  version : w64
  term : w64
  leader : List w8
  lastIdx : w64
  lastTerm : w64
  peers : List w8
  cfg : List w8
  cfgIdx : w64
  size : w64
  data : List w8

def encSnapReq (v : SnapReqV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.SnapReq"
    (strct [fStruct (encHdr v.hdr), fU64 v.version, fU64 v.term, fBytes v.leader, fU64 v.lastIdx,
      fU64 v.lastTerm, fBytes v.peers, fBytes v.cfg, fU64 v.cfgIdx, fU64 v.size, fBytes v.data])

/-- A `SnapResp`. -/
structure SnapRespV where
  failed : Bool
  err : List w8
  hdr : HdrV
  term : w64
  success : Bool

def encSnapResp (v : SnapRespV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.SnapResp"
    (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBool v.success])

def encTimeoutReq (h : HdrV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.TimeoutReq"
    (strct [fStruct (encHdr h)])

/-- A `TimeoutResp`. -/
structure TimeoutRespV where
  failed : Bool
  err : List w8
  hdr : HdrV

def encTimeoutResp (v : TimeoutRespV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/rpctransport.TimeoutResp"
    (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr)])

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
