/-
The wire values of go-craq's RPCs: the kit's generated codec (`examples/craqnet/rpc_gen.go`, by
`models/net/rpc/rpcgen.py`) as pure Lean functions of the abstract values. (The lab's `Wire.lean`
described its own kitgen codec; the names of the encodings are the lab's, the bytes rpcgen's.)

A top-level value is its type's name (`rpcPutTag`: the name's length, 8 bytes little-endian, and
its bytes) and the value. A string is its length and its bytes; a `uint64` 8 bytes little-endian;
a `bool` one byte; a byte slice its count and each byte as a `uint64`; a map its count and its
entries (key, value; in some order: `encPropReq`, `encPropResp` are relations); a slice its count
and its elements. A struct is the byte 1, then per field a byte 1 and the field's value if the
field is sent (not its zero value: gob's rule), else a byte 0.
-/
module

public import Perennial.Std.Word.LittleEndian
public import Perennial.Std.GMap
public import Perennial.Std.ByteString

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.despreston.go_craq

/-- A `uint64`. -/
def encU64 (x : w64) : List w8 := u64Le x

/-- A string: its length and its bytes. -/
def encStr (s : GoString) : List w8 := u64Le (W64 s.length) ++ s

/-- A byte slice: its count and each byte as a `uint64`. -/
def encBytes (s : List w8) : List w8 :=
  u64Le (W64 s.length) ++ (s.map fun b => u64Le (W64 (uint.Z b))).flatten

/-- A `bool`. -/
def encBool (b : Bool) : List w8 := [if b then W8 1 else W8 0]

/-- A struct field: sent (`1` and its value) or not (`0`). -/
def fld (sent : Bool) (body : List w8) : List w8 := if sent then W8 1 :: body else [W8 0]

def fStr (s : GoString) : List w8 := fld (decide (s ≠ [])) (encStr s)
def fBytes (s : List w8) : List w8 := fld (decide (s ≠ [])) (encBytes s)
def fU64 (x : w64) : List w8 := fld (decide (x ≠ W64 0)) (encU64 x)
def fBool (b : Bool) : List w8 := fld b (encBool b)

/-- A struct of the fields `fs`. -/
def strct (fs : List (List w8)) : List w8 := W8 1 :: fs.flatten

/-- A top-level value of the type named `t`. -/
def tagged (t : GoString) (body : List w8) : List w8 := encStr t ++ body

/-- `transport.NodeMeta`'s fields. -/
structure MetaV where
  isHead : Bool
  isTail : Bool
  prev : GoString
  next : GoString
  tail : GoString
deriving DecidableEq, Inhabited

def encString (s : GoString) : List w8 := tagged go!"string" (encStr s)
def encEmptyArgs : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport/netrpc.EmptyArgs" (strct [])
def encEmptyReply : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply" (strct [])
def encCommitArgs (k : GoString) (v : w64) : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport/netrpc.CommitArgs" (strct [fStr k, fU64 v])
def encClientWriteArgs (k x : GoString) : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport/netrpc.ClientWriteArgs"
    (strct [fStr k, fBytes x])
def encWriteArgs (k x : GoString) (v : w64) : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport/netrpc.WriteArgs"
    (strct [fStr k, fBytes x, fU64 v])
def encVersionResp (k : GoString) (v : w64) : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport/netrpc.VersionResponse"
    (strct [fStr k, fU64 v])
def encMeta (m : MetaV) : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport.NodeMeta"
    (strct [fBool m.isHead, fBool m.isTail, fStr m.prev, fStr m.next, fStr m.tail])
def encItem (k x : GoString) : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport.Item" (strct [fStr k, fBytes x])

/-- A `PropagateRequest` (`map[string]uint64`) with the entries `es` in this order. -/
def encPropReqL (es : List (GoString × w64)) : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport.PropagateRequest"
    (encU64 (W64 es.length) ++ (es.map fun e => encStr e.1 ++ encU64 e.2).flatten)

/-- A `[]ValueVersion`: `(value, version)` pairs. -/
def encVVs (vs : List (GoString × w64)) : List w8 :=
  encU64 (W64 vs.length) ++ (vs.map fun e => strct [fBytes e.1, fU64 e.2]).flatten

/-- A `PropagateResponse` (`map[string][]ValueVersion`) with the entries `es` in this order. -/
def encPropRespL (es : List (GoString × List (GoString × w64))) : List w8 :=
  tagged go!"github.com/despreston/go-craq/transport.PropagateResponse"
    (encU64 (W64 es.length) ++ (es.map fun e => encStr e.1 ++ encVVs e.2).flatten)

/-- The request's version of `k` (0 if absent). -/
def reqVer (req : GMap GoString w64) (k : GoString) : w64 := (req.lookup k).getD (W64 0)

/-- `es` lists the entries of `m`, each once. -/
def entriesOf {V : Type} (m : GMap GoString V) (es : List (GoString × V)) : Prop :=
  (es.map Prod.fst).Nodup ∧ ∀ k v, m.lookup k = some v ↔ (k, v) ∈ es

/-- `bs` encodes the request map `m` (its entries in some order). -/
def encPropReq (m : GMap GoString w64) (bs : List w8) : Prop :=
  ∃ es, entriesOf m es ∧ bs = encPropReqL es

/-- A key the protocol handles: at most 2 bytes (the kit's keys are `"k0"` and `"k1"`). A store
then has at most `1 + 256 + 256 ^ 2` keys, so a propagation request (a `map[string]uint64` of a
store's keys) fits the frames net/rpc's model reads (`maxFrameN`; `WireLen.lean`). -/
def keyOk (k : GoString) : Prop := k.length ≤ 2

theorem keyOk_lt {k : GoString} (h : keyOk k) : k.length < 256 := by unfold keyOk at h; omega

/-- A put the protocol handles: its key, and a value shorter than 256 bytes (the kit's bound). -/
def kvOk (k x : GoString) : Prop := keyOk k ∧ x.length < 256

/-- A request map's keys are keys the protocol handles. -/
def reqKeysOk (req : GMap GoString w64) : Prop := ∀ k v, req.lookup k = some v → keyOk k

/-- `bs` encodes the response map `m` (its entries in some order). -/
def encPropResp (m : GMap GoString (List (GoString × w64))) (bs : List w8) : Prop :=
  ∃ es, entriesOf m es ∧ bs = encPropRespL es

end github_com.despreston.go_craq

end Perennial
