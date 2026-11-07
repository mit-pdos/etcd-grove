/-
**A generic protobuf specification at the bytes** (2026-10-22, rafthttp stage 3): the vocabulary
of `proto.Size`, `proto.Marshal` and `proto.Unmarshal` for any message type, as grpc's messages
are specified (`ProtoMsg`, `Proof/google_golang_org/grpc/InvGrpc.lean`): one spec per function, for
every message type, and per Go type a record (`PbType`) whose instance is a trusted wire model of
that type. Lean-first; the design: `notes/decisions.md`, "A generic protobuf specification".

**A message type** (`PbType`): a protobuf message type `T` (passed as `*T`) with the model `M` of
its wire content;
- `ro l m`: a `*T` holding `m`, **read-only for good** (persistent): what `Size` and `Marshal` read.
  Because nothing can change it, its encoding is a function of its address (`pbEnc T.ty l`), which
  is what makes `Size` and `Marshal` of one message agree;
- `marshals m`: the messages whose encoding decodes back to them (e.g. raft's `Message` without
  `responses`, which the model's wire content leaves out; not an enum's range: protobuf-go keeps an
  undeclared value of a proto2 enum, `notes/rafthttp-plan.md`, "Open enums");
- `wire m bs`: `bs` is an encoding of `m` (what decoding `bs` gives back is `m`'s wire content);
- `eqv m m'`: `m` and `m'` have the same wire content (`proto.Clone` keeps it);
- `blank l`: a zero `*T` the receiver owns; `dec l m`: a decoded (or cloned) `*T` holding `m`,
  owned.

That `Marshal` of an `ro` at `m` (with `marshals m`) is a `wire` encoding of `m`, and that
`Unmarshal` of bytes into a `blank` gives a `dec` at some `m` of which the bytes are a `wire`
encoding, is what an instance asserts: each instance is a trusted wire model of its Go type (read
it against the type's `.proto`). The existing per-type statements (`proto.Marshal.spec` of an
`mvccpb.KeyValue`, `MarshalIRR`, `MarshalConfChange`, ...) predate this vocabulary.

**Per-type message models at their wire content** (stage A, the Scope's E, R and V for `PbType`,
revisions 4 to 6 with `[v6a]`; moved here from the prototype's `proto/PerType.lean`, CP2). Today's
`PbType` and its specs stay until the users are rewired (CP3); the per-type vocabulary sits next to
them:

- **The wire content `C`** of a message type: everything protobuf-go's `Marshal` reads (proto2
  presence, nil versus empty bytes, every level's unknown fields); `roC l c` a frozen message
  holding exactly `c`, `modelOf c` its model.
- **The unknown fields' validity**: `ufWire` (`UfWire.lean`) at every level (`T.levels c`):
  `ufValid c`. It is never `False` (`[]` satisfies it), but **the schemas and `levels` are trusted**
  (the Scope's T, `[v6a]` 1), each instance's against its Go descriptor: an under-declared schema
  (a declared number or wire type missing, e.g. a repeated scalar without its packed `LEN`) makes D2
  false (`uf` may then hold bytes the decoder turns into a known field, so
  `Unmarshal (Marshal c) ≠ c`); an over-declared one (a number the message does not have) makes D1
  false (Go's successful decode of such a field claims a `ufWire` it does not satisfy).
- **The data/encoder split** (`[v6]` §5 item 7): `PbModelC` is the type's data (its `PbType`, `C`,
  `roC`, `modelOf`, `levels`, `size`, `tree` and the proved `ro_iff`, `roC_ufValid`), a constant
  that mentions no axiom; `PbEncC T` its encoder part, the encoding `enc` and its one trusted fact
  `enc_ok`, a Prop field that each registered instance fills with its own axiom; `PbTypeC` the
  pair (`data`, `encd`), what the registry holds. `Sat` is stated over the data part, so a `Sat`
  theorem's axioms never include the instance's encoder axiom. `pbEncC T c` and `pbEncC_ok` are
  generic, a definition and a theorem: no generic trusted fact grows with the registrations.
- **The registry** `pbModelOf`, keyed on the Go type and taking the heap's instances (`hG`), so that
  a registration does not equate models across ghost heaps; one registration axiom per instance,
  of the exact shape `pbModelOf GF X.ty = some x`. The specs at a registered type
  (`proto.UnmarshalPbC.spec`, ...) quantify the registered pair only under the registration premise
  (`∀ I, pbModelOf GF I.data.ty = some I → …`): a caller never passes a model of its own.
- **`PbModelC.Sat`**: the decoded model `dec` is satisfiable by the generic store (`Store.lean`) of
  `T.tree m`, from a `blank` that is the zero struct (`BlankZero`).
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import Perennial.Proof.ProofPrelude
public import Proof.google_golang_org.protobuf.proto.UfWire
public import Proof.google_golang_org.protobuf.proto.Store

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A protobuf message type at the bytes** (see the file header). -/
structure PbType (GF : BundledGFunctors) where
  /-- The message's Go type `T` (the message is passed as `*T`). -/
  ty : go.GoType
  /-- The model of the message's wire content. -/
  M : Type
  /-- A `*T` holding `m`, read-only for good. -/
  ro : Loc → M → IProp GF
  ro_persistent : ∀ l m, Persistent (ro l m)
  /-- The messages whose encoding decodes back to them. -/
  marshals : M → Prop
  /-- `bs` is an encoding of `m`. -/
  wire : M → List w8 → Prop
  /-- `m` and `m'` have the same wire content (what `proto.Clone` keeps). -/
  eqv : M → M → Prop
  /-- A zero `*T` the receiver owns. -/
  blank : Loc → IProp GF
  /-- A decoded `*T` holding `m`, owned. -/
  dec : Loc → M → IProp GF

attribute [instance] PbType.ro_persistent

/-- **The encoding of the read-only-for-good `*T` at `l`** (`proto.Marshal`'s result, `proto.Size`
its length): a function of the address, since nothing can change the message (`PbType.ro`). -/
opaque pbEnc (ty : go.GoType) (l : Loc) : List w8

/-- **The trust boundary: what `pbEnc` is.** The encoding of a read-only-for-good `*T` holding `m`
is an encoding of `m` if `m` marshals (`T.wire`, the instance's wire model), and shorter than
`2^63` bytes (protobuf-go sizes it as an `int`). (2026-10-22, D38a: what `Size` and `Marshal`
return, stated of the message itself, so that a writer may be permitted the frame of an encoding
before the encoding is computed: the msgappv2 encoder writes the entries' count before it sizes
them.) -/
axiom pbEnc_ok (T : PbType GF) (l : Loc) (m : T.M) :
    T.ro l m ⊢ ⌜(T.marshals m → T.wire m (pbEnc T.ty l)) ∧ (pbEnc T.ty l).length < 2 ^ 63⌝

end defs

/-! ## The message type at its wire content -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A protobuf message type at its wire content: its data** (see the file header). -/
structure PbModelC (GF : BundledGFunctors) extends PbType GF where
  /-- Everything `Marshal` reads. -/
  C : Type
  /-- A frozen `*T` holding exactly `c`. -/
  roC : Loc → C → IProp GF
  roC_persistent : ∀ l c, Persistent (roC l c)
  /-- The model of a wire content. -/
  modelOf : C → M
  /-- Each level's schema and unknown fields (trusted: the file header). -/
  levels : C → List (FieldSchema × List w8)
  /-- protobuf's size formula. -/
  size : C → Nat
  /-- The normalizing store of a model (`Store.lean`). -/
  tree : M → VTree
  /-- `ro` is a frozen message at some wire content (proved). -/
  ro_iff : ∀ l m, ro l m ⊣⊢ ∃ c, roC l c ∗ ⌜modelOf c = m⌝
  /-- A frozen message's unknown fields are valid (proved, from `pbMsg`'s index). -/
  roC_ufValid : ∀ l c, roC l c ⊢ ⌜∀ p ∈ levels c, ufWire p.1 p.2⌝

attribute [instance] PbModelC.roC_persistent

/-- The unknown fields of every level are valid (a generic definition). -/
def PbModelC.ufValid (T : PbModelC GF) (c : T.C) : Prop := ∀ p ∈ T.levels c, ufWire p.1 p.2

/-- **A protobuf message type's encoder** (see the file header): an opaque per-type encoder and
its one trusted fact. -/
structure PbEncC (T : PbModelC GF) where
  /-- The encoding (an opaque per-type encoder). -/
  enc : T.C → List w8
  /-- **The type's one trusted fact** (filled by its axiom). -/
  enc_ok : ∀ c, T.marshals (T.modelOf c) → T.ufValid c → T.size c < 2 ^ 63 →
    T.wire (T.modelOf c) (enc c) ∧ (enc c).length = T.size c

/-- **A registered protobuf message type**: its data and its encoder. -/
structure PbTypeC (GF : BundledGFunctors) where
  data : PbModelC GF
  encd : PbEncC data

/-- **The registry of message types at their wire content** (`[v4]` R): one model per Go type,
per heap. Opaque: only the registration axioms say anything of it. -/
opaque pbModelOf {hlc : HasLC} (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp]
    [GoGlobalContext] [hG : HeapGS hlc GF] [go.Semantics] : go.GoType → Option (PbTypeC GF)

/-- **The encoding of a wire content** (generic: the instance's encoder). -/
def pbEncC (T : PbTypeC GF) (c : T.data.C) : List w8 := T.encd.enc c

/-- **What the encoding is** (a theorem, from the instance's `enc_ok` and `roC_ufValid`). -/
theorem pbEncC_ok (T : PbTypeC GF) (l : Loc) (c : T.data.C) :
    T.data.roC l c ⊢ ⌜T.data.marshals (T.data.modelOf c) → T.data.size c < 2 ^ 63 →
      T.data.wire (T.data.modelOf c) (pbEncC T c) ∧ (pbEncC T c).length = T.data.size c⌝ := by
  iintro #H
  ihave %Hu := T.data.roC_ufValid l c $$ H
  ipureintro
  intro hm hs
  exact T.encd.enc_ok c hm Hu hs

/-- **The decoded model is satisfiable** (V, `[v5a]`): from a blank message, the generic store of
the model's tree gives `dec` at the model. -/
def PbModelC.Sat (T : PbModelC GF) : Prop :=
  BlankZero T.ty T.blank ∧
    ∀ (m : T.M) (l : Loc), T.blank l ⊢ WP (storeInto T.ty l (T.tree m)) {{ _v, T.dec l m }}

end defs

end EtcdGrove
end Perennial
