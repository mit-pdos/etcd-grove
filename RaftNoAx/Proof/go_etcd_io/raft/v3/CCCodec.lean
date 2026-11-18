/-
The part's own (raft without hand-written axioms, `notes/raft-noax-codec.md`).

# The conf change codecs of `raftpb/noax.go`, pure

Pure functions over byte lists that mirror, statement by statement, the hand-written encoders and
decoders of the noax fork's `raftpb/noax.go` (`raft37-goose-lean-noax`, `91e2ea7`), so that the
proofs of the Go functions relate each loop or `if` to one equation:

* `ccVarint v` (`appendVarint`): the minimal varint (`varintEnc`, `UfWire.lean`);
  `ccEnumEnc t` (`appendEnum`): the varint of the sign extension; `ccBytesEnc v` (`appendBytes`):
  the length's varint, then the bytes; `ccEncOpt tag enc o` (one `if c.F != nil` block of an
  encoder): the tag and the value if the field is set.
* `ccVarintLoop`/`ccVarintL` (`consumeVarint`, the loop's state `n`, `i`, `v`, `shift` with the
  fuel `10 - n`), `ccEnumL` (`consumeEnum`), `ccFieldL` (`consumeField`, also `consumeBytes`,
  whose copy has the same contents), each from an index into the input, `none` where Go returns
  `false`.
* `ccOptField b i tag f` (one `if i < len(data) && data[i] == tag { ... }` block of a decoder).
* `ccDecodeSingle` (`unmarshalConfChangeSingle`), `ccChangesLoop` (`UnmarshalConfChangeV2`'s loop
  over the changes, with fuel). `ccDecodeV1`/`ccDecodeV2` (`CCModel.lean`) are the two decoders.
-/
module

public import Perennial.Proof.ProofPrelude
public import RaftNoAx.Proof.go_etcd_io.raft.v3.PbModel
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
          if 0 < n ∧ c = W8 0 then none
          else some (v ||| (W64 (uint.Z (c &&& W8 127)) <<< shift), i + 1)
        else ccVarintLoop b fuel (n + 1) (i + 1) (v ||| (W64 (uint.Z (c &&& W8 127)) <<< shift))
          (shift + W64 7)

/-- `consumeVarint(b, i)`. -/
def ccVarintL (b : List w8) (i : Nat) : Option (w64 × Nat) := ccVarintLoop b 10 0 i (W64 0) (W64 0)

/-- `consumeEnum(b, i)`: a varint that is the encoding of an `int32`. -/
def ccEnumL (b : List w8) (i : Nat) : Option (w32 × Nat) :=
  match ccVarintL b i with
  | none => none
  | some (v, j) =>
    if 2 ^ 31 ≤ uint.Z v ∧ uint.Z v < 0xffffffff80000000 then none else some (W32 (uint.Z v), j)

/-- `consumeField(b, i)` (and `consumeBytes`, whose fresh copy holds the same bytes): the
length-delimited value and the index after it. -/
def ccFieldL (b : List w8) (i : Nat) : Option (List w8 × Nat) :=
  match ccVarintL b i with
  | none => none
  | some (l, j) =>
    if (b.length : Int) - j < uint.Z l then none else some ((b.drop j).take (uint.nat l), j + uint.nat l)

/-- One `if i < len(data) && data[i] == tag { v, j, ok := f(data, i+1); if !ok { fail }; ...;
i = j }` block: the field's value if its tag is next, and the index after the block. -/
def ccOptField {α : Type} (b : List w8) (i : Nat) (tag : w8) (f : List w8 → Nat → Option (α × Nat)) :
    Option (Option α × Nat) :=
  if b[i]? = some tag then (f b (i + 1)).map fun p => (some p.1, p.2) else some (none, i)

/-- `unmarshalConfChangeSingle(data)`: the change's model (an unset field reads as zero, as its
getter), or `none`. -/
def ccDecodeSingle [GooseExts] (b : List w8) : Option ConfChangeSingleM :=
  (ccOptField b 0 (W8 8) ccEnumL).bind fun p1 =>
  (ccOptField b p1.2 (W8 16) ccVarintL).bind fun p2 =>
  if p2.2 = b.length then some ⟨p1.1.getD (W32 0), p2.1.getD (W64 0)⟩ else none

/-- `UnmarshalConfChangeV2`'s loop over the changes, from the index `i` with the changes `acc`
decoded so far; `fuel` bounds the iterations (each consumes at least two bytes). -/
def ccChangesLoop [GooseExts] (b : List w8) :
    Nat → Nat → List ConfChangeSingleM → Option (List ConfChangeSingleM × Nat)
  | 0, i, acc => some (acc, i)
  | fuel + 1, i, acc =>
    if b[i]? = some (W8 18) then
      match ccFieldL b (i + 1) with
      | none => none
      | some (v, j) =>
        match ccDecodeSingle v with
        | none => none
        | some s => ccChangesLoop b fuel j (acc ++ [s])
    else some (acc, i)

end EtcdGrove
end Perennial
