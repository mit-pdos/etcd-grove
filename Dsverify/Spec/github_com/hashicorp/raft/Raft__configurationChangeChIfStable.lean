/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__configurationChangeChIfStable.lean (241f27e).
-/
/-
`raft.(*Raft).configurationChangeChIfStable`'s spec (internal to the leader part of the main goroutine, MAIN-L). Returns `configurationChangeCh` (never sent on) or nil.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).configurationChangeChIfStable` (stage 4; stage 3: `configurationChangeCh` was never sent
on): `nil`, or `configurationChangeCh` (a bag of configuration change futures, `ccfP`) when the latest
configuration is the committed one and the commit index reached the commitment's start index; then a
recorded commit of the leader's term covers the latest configuration's index (what
`appendConfigurationEntry` needs, `gprot.leaderAppendCfg_upd`). -/
abbrev github_com.hashicorp.raft.Raft.configurationChangeChIfStable.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (cm : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s stLeader ∗ r.[Raft, go!"leaderState"].[leaderState, go!"commitment"] ↦ cm ∗
     isCommitment γ i s.term cm }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"configurationChangeChIfStable")) (Val #()))
  {{ (ch : Loc), RET #ch; r.[Raft, go!"leaderState"].[leaderState, go!"commitment"] ↦ cm ∗
      ((⌜ch = chan.nil⌝ ∗ mainOwnAt r γ rc i s stLeader) ∨
       (mainOwnAtSt r γ rc i s ∗ (∃ γq : ChanNames, isChanBag (V := Loc) γq ch (ccfP γ)) ∗
         (∃ k p : Nat, commitIs γ s.term k p ∗ ⌜lastCfgIdx s.log ≤ k⌝))) }}

end spec

end Perennial
