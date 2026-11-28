/-
`rpctransport.SnapReqBound`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `SnapReqBound(a)`: `snapBoundN` of the request's slices. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.SnapReqBound.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (w : SnapReq) (dq1 : DFrac) (id ad s0 s1 s2 s3 : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad ∗ w.Leader' ↦*{dq1} s0 ∗ w.Peers' ↦*{dq1} s1 ∗ w.Configuration' ↦*{dq1} s2 ∗ w.Data' ↦*{dq1} s3 }}
      (App (Val (@! SnapReqBound)) (Val #a))
    {{ (r : w64), RET #r; ⌜uint.nat r = snapBoundN id ad s0 s1 s2 s3⌝ ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad ∗ w.Leader' ↦*{dq1} s0 ∗ w.Peers' ↦*{dq1} s1 ∗ w.Configuration' ↦*{dq1} s2 ∗ w.Data' ↦*{dq1} s3 }}

end spec

end Perennial
