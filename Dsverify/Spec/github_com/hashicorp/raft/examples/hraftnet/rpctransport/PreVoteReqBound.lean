/-
`rpctransport.PreVoteReqBound`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `PreVoteReqBound(a)`: `preVoteBoundN` of the request's slices. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.PreVoteReqBound.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (w : PreVoteReq) (dq1 : DFrac) (id ad  : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad }}
      (App (Val (@! PreVoteReqBound)) (Val #a))
    {{ (r : w64), RET #r; ⌜uint.nat r = preVoteBoundN id ad⌝ ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad }}

end spec

end Perennial
