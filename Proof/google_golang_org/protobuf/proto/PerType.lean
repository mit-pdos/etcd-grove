/-
**Per-type message models, stage A prototype: the encoding at a registered type** (the Scope's E,
R and V for `PbType`, revisions 4, 5 and 5a). Prototype only: the real stage puts these fields in
`PbType` itself (`InvProto.lean`); here they extend it (`PbTypeC`), so that nothing that imports
`InvProto` rebuilds.

- **The wire content `C`** of a message type: everything protobuf-go's `Marshal` reads (proto2
  presence, nil versus empty bytes, every level's unknown fields); `roC l c` a frozen message
  holding exactly `c`, `modelOf c` its model.
- **The unknown fields' validity** (`ufWire`, one fixed definition): the bytes protobuf-go's decoder
  leaves in a level's unknown fields, read against the level's schema (`FieldSchema`): a sequence
  of well-formed fields, each top-level field's start tag a minimal varint (the decoder re-appends
  it with `AppendTag`; inside a group, tags and end tags are kept verbatim, possibly not minimal),
  groups balanced with matching numbers at every level and nested at most 10001 deep (measured:
  10001 decodes, 10002 fails), values verbatim, each field's number undeclared in the level or
  declared with a wire type its decoder does not take (`internal/impl/decode.go`'s `errUnknown`
  path). `ufValid c` is `ufWire` at every level (`T.levels c`): a wrong schema only weakens it;
  it is never `False` (`[]` satisfies it).
- **The encoding** `T.enc c`, exact in its size (`T.size c`, protobuf's formula, which counts an
  aliased submessage at each reference); its one trusted fact `T.enc_ok`, a Prop field that each
  registered instance fills with its own axiom. `pbEnc T c` and `pbEnc_ok` are generic, a
  definition and a theorem: no generic trusted fact grows with the registrations.
- **The registry** `pbModelOf`, keyed on the Go type and taking the heap's instances (`hG`), so that
  a registration does not equate models across ghost heaps; one registration axiom per instance,
  of the exact shape `pbModelOf GF X.ty = some x`.
- **`PbTypeC.Sat`**: the decoded model `dec` is satisfiable by the generic store (`Store.lean`) of
  `T.tree m`, from a `blank` that is the zero struct.
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto
public import Proof.google_golang_org.protobuf.proto.Store

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

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

/-- A field's tag: its number in `1 .. 2^29 - 1` and its wire type; minimal (`AppendTag`'s) or any
varint `ConsumeTag` accepts. -/
def TagOk (minimal : Bool) (num wt : Nat) (tag : List w8) : Prop :=
  1 ≤ num ∧ num < 2 ^ 29 ∧
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

/-! ## The message type at its wire content -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A protobuf message type at its wire content** (see the file header). -/
structure PbTypeC (GF : BundledGFunctors) extends PbType GF where
  /-- Everything `Marshal` reads. -/
  C : Type
  /-- A frozen `*T` holding exactly `c`. -/
  roC : Loc → C → IProp GF
  roC_persistent : ∀ l c, Persistent (roC l c)
  /-- The model of a wire content. -/
  modelOf : C → M
  /-- Each level's schema and unknown fields. -/
  levels : C → List (FieldSchema × List w8)
  /-- protobuf's size formula. -/
  size : C → Nat
  /-- The encoding (an opaque per-type encoder). -/
  enc : C → List w8
  /-- **The type's one trusted fact** (filled by its axiom). -/
  enc_ok : ∀ c, marshals (modelOf c) → (∀ p ∈ levels c, ufWire p.1 p.2) → size c < 2 ^ 63 →
    wire (modelOf c) (enc c) ∧ (enc c).length = size c
  /-- The normalizing store of a model (`Store.lean`). -/
  tree : M → VTree
  /-- `ro` is a frozen message at some wire content (proved). -/
  ro_iff : ∀ l m, ro l m ⊣⊢ ∃ c, roC l c ∗ ⌜modelOf c = m⌝
  /-- A frozen message's unknown fields are valid (proved, from `pbMsg`'s index). -/
  roC_ufValid : ∀ l c, roC l c ⊢ ⌜∀ p ∈ levels c, ufWire p.1 p.2⌝

attribute [instance] PbTypeC.roC_persistent

/-- The unknown fields of every level are valid (a generic definition). -/
def PbTypeC.ufValid (T : PbTypeC GF) (c : T.C) : Prop := ∀ p ∈ T.levels c, ufWire p.1 p.2

/-- **The registry of message types at their wire content** (`[v4]` R): one model per Go type,
per heap. Opaque: only the registration axioms say anything of it. -/
opaque pbModelOf {hlc : HasLC} (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp]
    [GoGlobalContext] [hG : HeapGS hlc GF] [go.Semantics] : go.GoType → Option (PbTypeC GF)

/-- **The encoding of a wire content** (generic: the instance's encoder). -/
def pbEncC (T : PbTypeC GF) (c : T.C) : List w8 := T.enc c

/-- **What the encoding is** (a theorem, from the instance's `enc_ok` and `roC_ufValid`). -/
theorem pbEncC_ok (T : PbTypeC GF) (l : Loc) (c : T.C) :
    T.roC l c ⊢ ⌜T.marshals (T.modelOf c) → T.size c < 2 ^ 63 →
      T.wire (T.modelOf c) (pbEncC T c) ∧ (pbEncC T c).length = T.size c⌝ := by
  iintro #H
  ihave %Hu := T.roC_ufValid l c $$ H
  ipureintro
  intro hm hs
  exact T.enc_ok c hm Hu hs

/-- **`blank` is the zero struct** of the type at some Lean representation. -/
def BlankZero (ty : go.GoType) (blank : Loc → IProp GF) : Prop :=
  ∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V) (_ : IntoValTyped (GF := GF) V ty),
    ∀ l, blank l ⊣⊢ l ↦ zero_val V

/-- **The decoded model is satisfiable** (V, `[v5a]`): from a blank message, the generic store of
the model's tree gives `dec` at the model. -/
def PbTypeC.Sat (T : PbTypeC GF) : Prop :=
  BlankZero T.ty T.blank ∧
    ∀ (m : T.M) (l : Loc), T.blank l ⊢ WP (storeInto T.ty l (T.tree m)) {{ _v, T.dec l m }}

end defs

end EtcdGrove
end Perennial
