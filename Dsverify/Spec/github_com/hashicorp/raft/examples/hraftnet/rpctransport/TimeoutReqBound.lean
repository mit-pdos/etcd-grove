/-
`rpctransport.TimeoutReqBound`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Wire

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `TimeoutReqBound(a)`: `timeoutBoundN` of the request's slices. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.TimeoutReqBound.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (w : TimeoutReq) (dq1 : DFrac) (id ad  : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad }}
      (App (Val (@! TimeoutReqBound)) (Val #a))
    {{ (r : w64), RET #r; ⌜uint.nat r = timeoutBoundN id ad⌝ ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad }}

end spec

end Perennial
