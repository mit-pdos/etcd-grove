/-
`appendOversizedBlock(b, kind)` (the grpc model's `model_wire.go`, F1 of `notes/phase7-plan.md`
§0a): `b` with the marker of a block of kind `kind` over the limit after it
(`srvFrameBytes (.oversized kind)`).
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
abbrev grpc.appendOversizedBlock.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (kind : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* vs ∗
      ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (@! google_golang_org.grpc.appendOversizedBlock)) (Val #b)) (Val #kind))
  {{ (r : GoSlice), RET #r; r ↦* (vs ++ srvFrameBytes (.oversized kind)) ∗
      ownSliceCap w8 r (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
