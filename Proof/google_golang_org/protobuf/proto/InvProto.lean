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
- `marshals m`: the messages whose encoding decodes back to them (e.g. no out-of-range value of a
  closed proto2 enum, which a decoder puts in the unknown fields);
- `wire m bs`: `bs` is an encoding of `m` (what decoding `bs` gives back is `m`'s wire content);
- `blank l`: a zero `*T` the receiver owns; `dec l m`: a decoded `*T` holding `m`, owned.

That `Marshal` of an `ro` at `m` (with `marshals m`) is a `wire` encoding of `m`, and that
`Unmarshal` of bytes into a `blank` gives a `dec` at some `m` of which the bytes are a `wire`
encoding, is what an instance asserts: each instance is a trusted wire model of its Go type (read
it against the type's `.proto`). The existing per-type statements (`proto.Marshal.spec` of an
`mvccpb.KeyValue`, `MarshalIRR`, `MarshalConfChange`, ...) predate this vocabulary.
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  /-- A zero `*T` the receiver owns. -/
  blank : Loc → IProp GF
  /-- A decoded `*T` holding `m`, owned. -/
  dec : Loc → M → IProp GF

attribute [instance] PbType.ro_persistent

/-- **The encoding of the read-only-for-good `*T` at `l`** (`proto.Marshal`'s result, `proto.Size`
its length): a function of the address, since nothing can change the message (`PbType.ro`). -/
opaque pbEnc (ty : go.GoType) (l : Loc) : List w8

end defs

end EtcdGrove
end Perennial
