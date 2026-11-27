/-
`appendData(b, hdr, payload)` (the grpc model's `model_wire.go`): `b` with a data frame after it:
the kind `frameData`, the message header `hdr` and the payload. With `hdr = grpcMsgHdr bs` and
`payload = bs`, what it appends is `dataFrame bs` (`appendData_dataFrame`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcWire

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
abbrev grpc.appendData.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (hdr : GoSlice) (hd : List w8) (dqh : DFrac)
    (pl : GoSlice) (ps : List w8) (dqp : DFrac),
  {{ (b ↦* vs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ hdr ↦*{dqh} hd ∗ pl ↦*{dqp} ps : IProp GF) }}
    (App (App (App (Val (@! google_golang_org.grpc.appendData)) (Val #b)) (Val #hdr)) (Val #pl))
  {{ (r : GoSlice), RET #r; r ↦* (vs ++ frameData :: (hd ++ ps)) ∗
      ownSliceCap w8 r (DFrac.own 1) ∗ hdr ↦*{dqh} hd ∗ pl ↦*{dqp} ps }}

end spec

end EtcdGrove
end Perennial
