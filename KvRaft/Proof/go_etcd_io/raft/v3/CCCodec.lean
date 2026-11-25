-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/CCCodec.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The part's own (raft without hand-written axioms, `notes/raft-noax-codec.md`).

# The conf change codecs of `raftpb/noax.go`, pure

The noax fork reads fields in wire order. `ccTagL` reads the tag, the three
field handlers update message values, and `ccSkipField` consumes an unknown
scalar or an entire balanced group. `ccWireLoop` stops at the end of the
input or at the first malformed field. `ccEncOpt` models presence when
encoding known fields. Unknown fields follow the known fields on the wire.
-/
module

public import Perennial.Proof.ProofPrelude
public import KvRaft.Proof.go_etcd_io.raft.v3.PbModel
public import Proof.google_golang_org.protobuf.proto.UfWire

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-! ## Encoders -/

/-- `appendVarint(b, v)` appends `ccVarint v`. -/
def ccVarint (v : w64) : List w8 := varintEnc (uint.nat v)

/-- `appendEnum(b, v)` appends `ccEnumEnc v`: the varint of `uint64(int64(v))`. -/
def ccEnumEnc (t : w32) : List w8 := ccVarint (W64 (sint.Z t))

/-- `appendBytes(b, v)` appends `ccBytesEnc v`: `uint64(len(v))`'s varint, then `v`. -/
def ccBytesEnc (v : List w8) : List w8 := ccVarint (W64 v.length) ++ v

/-- One `if c.F != nil { b = append(b, tag); b = appendX(b, ...) }` block: nothing for an unset
field, the tag then the value's encoding for a set one. -/
def ccEncOpt {α : Type} (tag : w8) (enc : α → List w8) : Option α → List w8
  | none => []
  | some a => tag :: enc a

/-- `MarshalConfChangeV1` of a message whose `Id`, `Type`, `NodeId`, `Context` are `id`, `ty`,
`nid`, `ctx` (`none` for a `nil` field). -/
def ccEncodeV1 (id : Option w64) (ty : Option w32) (nid : Option w64) (ctx : Option (List w8)) :
    List w8 :=
  ccEncOpt (W8 8) ccVarint id ++ ccEncOpt (W8 16) ccEnumEnc ty ++ ccEncOpt (W8 24) ccVarint nid ++
    ccEncOpt (W8 34) ccBytesEnc ctx

/-- `marshalConfChangeSingle` of a non-`nil` change whose `Type`, `NodeId` are `ty`, `nid`. -/
def ccEncodeSingle (ty : Option w32) (nid : Option w64) : List w8 :=
  ccEncOpt (W8 8) ccEnumEnc ty ++ ccEncOpt (W8 16) ccVarint nid

/-- The changes' part of `MarshalConfChangeV2`: each change's encoding `c` as the field
`tag 18, ccBytesEnc c`. -/
def ccEncChanges : List (List w8) → List w8
  | [] => []
  | c :: cs => (W8 18 :: ccBytesEnc c) ++ ccEncChanges cs

/-- `MarshalConfChangeV2` of a message whose `Transition` is `t`, whose changes encode to `chs`
(`marshalConfChangeSingle` of each) and whose `Context` is `ctx`. -/
def ccEncodeV2 (t : Option w32) (chs : List (List w8)) (ctx : Option (List w8)) : List w8 :=
  ccEncOpt (W8 8) ccEnumEnc t ++ ccEncChanges chs ++ ccEncOpt (W8 26) ccBytesEnc ctx

/-! ## Decoders -/

/-- `consumeVarint`'s loop from the iteration `n` (fuel `10 - n`), at the index `i`, with the value
`v` decoded so far and the next byte's `shift`: `some (value, index after it)`, or `none` where Go
returns `false`. -/
def ccVarintLoop (b : List w8) : Nat → Nat → Nat → w64 → w64 → Option (w64 × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, n, i, v, shift =>
    match b[i]? with
    | none => none
    | some c =>
      if n = 9 ∧ 1 < uint.Z c then none
      else
        if uint.Z c < 128 then
          some (v ||| (W64 (uint.Z (c &&& W8 127)) <<< shift), i + 1)
        else ccVarintLoop b fuel (n + 1) (i + 1) (v ||| (W64 (uint.Z (c &&& W8 127)) <<< shift))
          (shift + W64 7)

/-- `consumeVarint(b, i)`. -/
def ccVarintL (b : List w8) (i : Nat) : Option (w64 × Nat) := ccVarintLoop b 10 0 i (W64 0) (W64 0)

/-- `consumeEnum(b, i)`: the low 32 bits of a varint. -/
def ccEnumL (b : List w8) (i : Nat) : Option (w32 × Nat) :=
  match ccVarintL b i with
  | none => none
  | some (v, j) =>
    some (W32 (uint.Z v), j)

/-- `consumeField(b, i)` (and `consumeBytes`, whose fresh copy holds the same bytes): the
length-delimited value and the index after it. -/
def ccFieldL (b : List w8) (i : Nat) : Option (List w8 × Nat) :=
  match ccVarintL b i with
  | none => none
  | some (l, j) =>
    if (b.length : Int) - j < uint.Z l then none else some ((b.drop j).take (uint.nat l), j + uint.nat l)

/-- Read a wire tag. Message fields and fields inside unknown groups have
different upper bounds in protobuf-go. -/
def ccTagL (b : List w8) (i maxField : Nat) : Option (Nat × Nat) := do
  let (v, j) ← ccVarintL b i
  let tag := uint.nat v
  if 1 ≤ tag / 8 ∧ tag / 8 ≤ maxField then some (tag, j) else none

/-- The end of a scalar wire value of the given type. -/
def ccSkipScalar (b : List w8) (i : Nat) : Nat → Option Nat
  | 0 => (ccVarintL b i).map Prod.snd
  | 1 => if i + 8 ≤ b.length then some (i + 8) else none
  | 2 => (ccFieldL b i).map Prod.snd
  | 5 => if i + 4 ≤ b.length then some (i + 4) else none
  | _ => none

/-- Match closing tags against the stack of open field numbers. Each
iteration reads at least one tag byte. The outer group occupies one slot. -/
def ccGroupLoop (b : List w8) : Nat → Nat → List Nat → Option Nat
  | _, i, [] => some i
  | 0, _, _ :: _ => none
  | fuel + 1, i, num :: outer => do
    let (tag, start) ← ccTagL b i (2 ^ 31 - 1)
    match tag % 8 with
    | 3 => if outer.length + 1 ≤ 10000 then
             ccGroupLoop b fuel start (tag / 8 :: num :: outer)
           else none
    | 4 => if tag / 8 = num then ccGroupLoop b fuel start outer else none
    | wt => ccGroupLoop b fuel (← ccSkipScalar b start wt) (num :: outer)

/-- Continue decoding an unknown group at a wire boundary. -/
def ccGroupAt (b : List w8) (i : Nat) (opened : List Nat) : Option Nat :=
  ccGroupLoop b (b.length - i) i opened

/-- End of the field value whose tag has already been consumed. -/
def ccSkipField (b : List w8) (i tag : Nat) : Option Nat :=
  if tag % 8 = 3 then ccGroupAt b i [tag / 8]
  else ccSkipScalar b i (tag % 8)

/-- Decode fields in wire order, carrying the getters' values. A successful
iteration consumes the tag and value. The input length bounds their number. -/
def ccWireLoop {α : Type} (b : List w8)
    (field : Nat → Nat → α → Option (α × Nat)) : Nat → Nat → α → Option α
  | 0, i, state => if i = b.length then some state else none
  | fuel + 1, i, state => do
    if i = b.length then return state
    let (tag, start) ← ccTagL b i (2 ^ 29 - 1)
    let (next, j) ← field tag start state
    ccWireLoop b field fuel j next

/-- Decode the remaining fields starting at an input boundary. -/
def ccWireAt {α : Type} (b : List w8) (field : Nat → Nat → α → Option (α × Nat))
    (i : Nat) (state : α) : Option α := ccWireLoop b field (b.length - i) i state

/-- The nested change's scalar fields have wire tags 8 and 16. -/
def ccSingleField [GooseExts] (b : List w8) (tag i : Nat)
    (state : ConfChangeSingleM) : Option (ConfChangeSingleM × Nat) := do
  match tag with
  | 8 =>
    let (val, j) ← ccEnumL b i
    return (⟨val, state.NodeId'⟩, j)
  | 16 =>
    let (val, j) ← ccVarintL b i
    return (⟨state.Type', val⟩, j)
  | _ => return (state, ← ccSkipField b i tag)

def ccWireSingle [GooseExts] (b : List w8) : Option ConfChangeSingleM :=
  ccWireAt b (ccSingleField b) 0 ⟨W32 0, W64 0⟩

end EtcdGrove
end Perennial
