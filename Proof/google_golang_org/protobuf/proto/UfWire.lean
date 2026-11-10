/-
**The unknown fields protobuf-go's decoder leaves** (per-type message models, stage A: the Scope's
`[v6]` §2, `ufWire`; moved here from the stage A prototype's `proto/PerType.lean`, CP2): the bytes
in a level's unknown fields, read against the level's schema (`FieldSchema`): a sequence of
well-formed fields, each top-level field's start tag a minimal varint (the decoder re-appends it
with `AppendTag`; inside a group, tags and end tags are kept verbatim, possibly not minimal), groups
balanced with matching numbers at every level and nested at most 10001 deep (measured: 10001
decodes, 10002 fails), values verbatim, each field's number undeclared in the level or declared with
a wire type its decoder does not take (`internal/impl/decode.go`'s `errUnknown` path). Pure: below
both the raft messages' hidden-field invariant (`pbMsg`, `InvPb.lean`) and the generic protobuf
vocabulary (`InvProto.lean`).
-/
module

public import Perennial.Proof.ProofPrelude

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-! ## The unknown fields, as protobuf-go's decoder leaves them -/

section wire

/-- The minimal varint encoding of `n` (what `protowire.AppendVarint` writes). -/
def varintEnc (n : Nat) : List w8 :=
  if h : n < 128 then [W8 n] else W8 (n % 128 + 128) :: varintEnc (n / 128)
termination_by n
decreasing_by omega

/-- The value of a varint's bytes (the low 7 bits of each, little-endian). -/
def varintVal : List w8 → Nat
  | [] => 0
  | b :: bs => b.toNat % 128 + 128 * varintVal bs

/-- `bs` is one varint as `protowire.ConsumeVarint` accepts it: at most 10 bytes, every byte but
the last with its continuation bit, a value below `2^64`; possibly not minimal. -/
def IsVarint (bs : List w8) : Prop :=
  1 ≤ bs.length ∧ bs.length ≤ 10 ∧ (∀ (i : Nat) (h : i + 1 < bs.length), 128 ≤ (bs[i]'(by omega)).toNat) ∧
    (∀ b, bs.getLast? = some b → b.toNat < 128) ∧ varintVal bs < 2 ^ 64

/-- A field's tag: its number and its wire type; a top-level unknown field's (`minimal`): number in
`1 .. 2^29 - 1`, the minimal varint (`AppendTag`'s); a tag inside an unknown group (kept verbatim):
number in `1 .. 2^31 - 1` (`protowire.ConsumeTag`, measured), any varint it accepts. -/
def TagOk (minimal : Bool) (num wt : Nat) (tag : List w8) : Prop :=
  1 ≤ num ∧ num < (if minimal then 2 ^ 29 else 2 ^ 31) ∧
    (if minimal then tag = varintEnc (num * 8 + wt) else IsVarint tag ∧ varintVal tag = num * 8 + wt)

mutual
/-- `bs` is the value of a field numbered `num` of wire type `wt`, as `protowire.ConsumeFieldValue`
accepts it, its groups nested at most `d` deep: a varint (0), 8 bytes (1), a length-delimited
value (2), a group closed by the end-group tag of the same number (3), 4 bytes (5). -/
inductive WVal : Nat → Nat → Nat → List w8 → Prop
  | varint (d num : Nat) (bs : List w8) : IsVarint bs → WVal d num 0 bs
  | i64 (d num : Nat) (bs : List w8) : bs.length = 8 → WVal d num 1 bs
  | len (d num : Nat) (pre body : List w8) : IsVarint pre → varintVal pre = body.length →
      WVal d num 2 (pre ++ body)
  | group (d num : Nat) (body etag : List w8) : WFields d body → TagOk false num 4 etag →
      WVal (d + 1) num 3 (body ++ etag)
  | i32 (d num : Nat) (bs : List w8) : bs.length = 4 → WVal d num 5 bs

/-- `bs` is a sequence of whole fields (inside a group: any tags, values verbatim). -/
inductive WFields : Nat → List w8 → Prop
  | nil (d : Nat) : WFields d []
  | cons (d num wt : Nat) (tag v rest : List w8) : TagOk false num wt tag → WVal d num wt v →
      WFields d rest → WFields d (tag ++ v ++ rest)
end

/-- **A level's schema**: each declared field number with the wire types its decoder takes (a
repeated scalar: its own and the packed `LEN`). -/
abbrev FieldSchema : Type := List (Nat × List Nat)

/-- The decoder routes a field numbered `num` of wire type `wt` to the unknown fields: the level
does not declare `num`, or does not take `wt` for it. -/
def Routed (s : FieldSchema) (num wt : Nat) : Prop :=
  ∀ p ∈ s, p.1 = num → wt ∉ p.2

/-- **`uf` is what protobuf-go's decoder leaves in the unknown fields of a level of schema `s`**:
whole fields, each with a minimal outer start tag (inner tags and end tags verbatim), groups at
most 10001 deep, each routed there. -/
inductive ufWire (s : FieldSchema) : List w8 → Prop
  | nil : ufWire s []
  | cons (num wt : Nat) (tag v rest : List w8) : TagOk true num wt tag → WVal 10001 num wt v →
      Routed s num wt → ufWire s rest → ufWire s (tag ++ v ++ rest)

theorem ufWire_nil (s : FieldSchema) : ufWire s [] := .nil

/-- The size of the minimal varint of `n`. -/
def varintSize (n : Nat) : Nat := (varintEnc n).length

end wire

end EtcdGrove
end Perennial
