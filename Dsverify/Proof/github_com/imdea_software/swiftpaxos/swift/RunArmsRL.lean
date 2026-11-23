/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunArmsRL.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's own arms of `swift.RunArms` over `swift.runInv` (the run-loop side's; the
descriptor and recovery arms are the other sides', notes/prove-swift.md §22):

* `swift.runArm_leader`: `r.leader()` (`replica.Leader(r.ballot, r.N)`), the `leader` arm.
* `swift.runArm_propose` (round 18): `r.handleProposal(gp)`, the `propose` arm, over
  `handleProposal.specI DS` (HandleProposal.lean, round 20) at `DS := descDSN γ γc γm x` (round 24)
  (round 19/D20: `runInv` holds `descDS`, RunInvD.lean; the run loop's numbering `seqOwn`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunInvD
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWith
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- The `leader` arm: `r.leader()` reads the run loop's quarter of `ballot` and the replica's
`N`. -/
theorem swift.runArm_leader (wp_Leader : replica.Leader.spec) (rp : Loc) (γ : sp.Names)
    (γc γm : GName) (x : swift.RunX) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"leader")) (Val #()))
    {{ (ld : w32), RET #ld; swift.runInv rp γ γc γm x }} := by
  wp_start as Hinv
  iunfold swift.runInv at Hinv
  icases Hinv with ⟨#Hd, Hs, Hrl, ⟨%ld, %v, %M, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
  ihave #Hd' := Hd
  iunfold swift.descCtxE at Hd'
  icases Hd' with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep,
    %Hids, -⟩
  ihave #Hrep2 := Hrep
  iunfold replica.isReplica at Hrep2
  icases Hrep2 with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hq, #HN, -⟩
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hrest⟩
  wp_auto
  wp_apply wp_Leader
  · ipureintro
    obtain ⟨-, -, -, h1, h7, -⟩ := Hids
    constructor <;> word
  iapply HΦ
  iunfold swift.runInv
  iframe Hd Hs Hrl Hdr Hrf Hds Hseq
  iexists ld, v, M, bs, hd, w
  isplitl [Hbal Hrest]
  · iunfold swift.runSt
    iframe Hbal Hrest
  iframe Hpd
  ipureintro; exact Hn

/-- The `propose` arm: `r.handleProposal(gp)` over `runInv` (its descriptor part `descDS` is
the `DS` handleProposal threads through; the numbering `seqOwn`). -/
theorem swift.runArm_propose (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_hp : x.str = swift.cmdStr →
      swift.Replica.handleProposal.specIN (hG := hG) (swift.descDSNo γ γc γm x))
    (gp : Loc) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗ sp.proposeP γ gp }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleProposal")) (Val #gp))
    {{ RET #(); swift.runInv rp γ γc γm x }} := by
  iintro %Φ ⟨#Hpkg, Hinv, Hprop⟩ HΦ
  ihave ⟨#Hctx, Hinv⟩ := BI.persistent_entails_right (swift.runInv_ctx rp γ γc γm x) $$ Hinv
  iunfold swift.runInv at Hinv
  icases Hinv with ⟨#Hd, Hs, Hrl, ⟨%ld, %v, %M, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
  ihave ⟨%Hstr, Hrl⟩ := BI.persistent_entails_right (swift.runLoopCtx_str rp γ γc γm x) $$ Hrl
  -- round 37b (table rev 8c, GAP-37b/37d): `proposeCtxB` and the history from `runLoopCtx`
  ihave ⟨#Hown, Hrl⟩ := BI.persistent_entails_right (swift.runLoopCtx_ownB rp γ γc γm x) $$ Hrl
  ihave ⟨#HdC, Hds⟩ := BI.persistent_entails_right (swift.descDS_ctx γ γc γm x rp) $$ Hds
  ihave ⟨#HpB, #Hhist⟩ := Hown $$ HdC
  ihave Hds : swift.descDSNo γ γc γm x γ x.γcl x.γdl x.N x.r rp $$ [Hds]
  · iunfold swift.descDSNo
    isplitl
    · iunfold swift.descDSN; iframe Hds HpB Hhist
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      unfold swift.DC.ctx; iexact Hd
    ipureintro; rfl
  iapply (wp_hp Hstr γ γc γm x.γl x.γw x.γv x.γe x.γo x.sn x.γdl rp gp x.N x.r x.k ld v M bs hd w)
    $$ [Hrun Hseq Hdr Hds Hpd Hprop]
  · iframe #; iframe; ipureintro; exact Hn
  inext
  iintro ⟨%v', %hd', %w', Hrun, Hseq, Hdr, Hds, Hpd, %Hw'⟩
  iunfold swift.descDSNo at Hds
  icases Hds with ⟨Hds, -⟩
  iunfold swift.descDSN at Hds
  icases Hds with ⟨Hds, -, -⟩
  iapply HΦ
  iunfold swift.runInv
  iframe Hd Hs Hrl Hdr Hrf Hds Hseq
  iexists ld, v', M, bs, hd', w'
  iframe
  ipureintro; exact Hw'.2.2

end proof

end Perennial.github_com.imdea_software.swiftpaxos
