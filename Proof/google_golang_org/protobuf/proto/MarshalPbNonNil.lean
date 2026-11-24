/-
**`proto.Marshal` returns a non-nil slice** (P6, the torn-`Save` fix): `proto.MarshalPb.spec` with
`d ≠ slice.nil` added to its post, for a non-nil message. Not an axiom: an `abbrev … .law`, a hypothesis
of the proofs that need it (the WAL's empty state record, `WalPbIn.ZeroStLaw`), pending the
strengthening of the trusted `proto.MarshalPb.spec` (requested on #8, `notes/wal-p6-handoff.md`, "The
hard stop"); once that lands, this law is that spec and the hypothesis is discharged by its axiom.

Against protobuf-go v1.36.12 (`proto/encode.go:119-146`): an empty encoding is
`emptyBytesForMessage(m)`, the non-nil `emptyBuf[:]` for a valid message (a non-nil `*T`). Lean-first.
-/
module

public import Spec.google_golang_org.protobuf.proto.MarshalPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.MarshalPb.spec` with a non-nil result for a non-nil message. -/
abbrev proto.MarshalPbNonNil.law : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF I.data.ty = some I →
  ∀ (l : Loc) (c : I.data.C), l ≠ null → I.data.marshals (I.data.modelOf c) → I.data.size c < 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ I.data.roC l c }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType I.data.ty) #l)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      d ↦* pbEncC I c ∗ ownSliceCap w8 d (DFrac.own 1) ∗ ⌜d ≠ slice.nil⌝ }}

end law

end EtcdGrove
end Perennial
