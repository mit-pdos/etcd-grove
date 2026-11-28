/-
`appendHeaderBlock(b, kind, fields)` (the grpc model's `model_wire.go`): `b` with the header block
`headerBlock kind fs` of the fields after it, when their list is within the receiver's limit
(`headerListOk`, what every caller checks first with `headerListTooLarge`), so that every length
fits its `uint32` (F1 of `notes/phase7-plan.md` §0a).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcWire
public import Perennial.Proof.encoding.binary.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev grpc.appendHeaderBlock.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (kind : w8) (s : GoSlice)
    (hs : List google_golang_org.grpc.headerField) (dq : DFrac),
  headerListOk (hfPairs hs) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* vs ∗
      ownSliceCap w8 b (DFrac.own 1) ∗ s ↦*{dq} hs }}
    (App (App (App (Val (@! google_golang_org.grpc.appendHeaderBlock)) (Val #b)) (Val #kind))
      (Val #s))
  {{ (r : GoSlice), RET #r; r ↦* (vs ++ headerBlock kind (hfPairs hs)) ∗
      ownSliceCap w8 r (DFrac.own 1) ∗ s ↦*{dq} hs }}

end spec

end EtcdGrove
end Perennial
