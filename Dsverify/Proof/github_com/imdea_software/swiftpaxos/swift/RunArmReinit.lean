/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunArmReinit.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's `reinit` arm (round 31, sv-swc; prove-swift.md §36): `r.reinitNewLeaderAckNs(b)`
over `swift.runInv` (RunInvD.lean). Round 33 (F2', D30): it first stores `b` in
`r.newLeaderAckNsBallot` (`runFields`' `bs`), and the new set's messages are at `b`
(`swift.nlP γ N b`). It replaces `r.newLeaderAckNs` (nil or a set, `swift.nlSet`,
RunInv.lean) by `ReinitMsgSet(NewMajorityOf(N), accept, free, r.handleNewLeaderAckNs)`
(`replica.mset.MsgSet.ReinitMsgSet.specD`): the set's data with the method value as handler,
its messages with `swift.nlP`. The two literal closures (`accept` returns true, `free` does
nothing) meet `acceptOk`/`freeOk` with `RA := True`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmRec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

set_option goose.wp.extras true

/-- **The `reinit` arm** (see the file header). -/
theorem swift.runArm_reinit (wp_NM : replica.NewMajorityOf.spec (hG := hG))
    (wp_Re : replica.mset.MsgSet.ReinitMsgSet.specD (hG := hG))
    (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (b : w32) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗ swift.ownBallot rp b }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"reinitNewLeaderAckNs"))
        (Val #b))
    {{ RET #(); swift.runInv rp γ γc γm x }} := by
  wp_start as ⟨HI, #Hob⟩
  ihave ⟨#Hctx, HI⟩ := BI.persistent_entails_right (swift.runInv_ctx rp γ γc γm x) $$ HI
  iunfold swift.runInv at HI
  icases HI with ⟨#Hd, Hs, Hrl, Hrun, Hseq, Hdr, Hrf, Hds⟩
  iunfold swift.runCtxD at Hctx
  icases Hctx with ⟨%rr, %me, %fr, %l', %dm, #Hrr, #Hrep, %Hids, -, -, -, -, -, -, -⟩
  ihave #Hrep2 := Hrep
  iunfold replica.isReplica at Hrep2
  icases Hrep2 with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, -, -, #HN, #Hid, -⟩
  iunfold swift.runFields at Hrf
  icases Hrf with ⟨%t, %fq, %rc, %nl, %bs, %ppsl, %pp, Ft, FFQ, Frc, Fnl, Fbs, Hnl, FPP, Hpp, %Hpp, %Hnlr⟩
  have hN7 : x.N ≤ 7 := Hids.2.2.2.2.1
  -- D56 N1-c: `b` is an own ballot (`RunArms.recBal`'s post), so `r` leads it
  ihave %Hobv := swift.ownBallot_val rp rr x.N me b hN7 $$ [Hrr HN Hid Hob]
  · iframe #
  have hlead : sp.leaderOf x.N (sp.bal b) = x.r := by
    rw [swift.leaderOf_emod Hobv.1 Hids.2.1 Hids.2.2.2.1 Hobv.2]; exact Hids.1
  wp_auto
  wp_apply (wp_NM x.N)
  · ipureintro; omega
  try wp_auto
  rw [show ((x.N : Int) / 2 + 1) = ((x.N / 2 + 1 : Nat) : Int) by omega]
  iunfold swift.nlSet at Hnl
  isimp only [swift.nlQ, swift.nlHd] at Hnl
  wp_apply (wp_Re nl (interface.mkOk replica.Majority.ty #(W64 ((x.N / 2 + 1 : Nat) : Int))) (x.N / 2 + 1) (fun _ => True) (swift.nlP γ x.N b)
    (fun _ _ => iprop(True)) (fun _ => iprop(False)) iprop(True) _ _
    (methods (go.GoType.PointerType swift.Replica.ty) go!"handleNewLeaderAckNs" #rp)) $$ [Hnl]
    as %nl' Hnl'
  · isplitr
    · iunfold replica.mset.quorumIs
      isplitr
      · ipureintro; omega
      ileft; ipureintro; exact ⟨Or.inl rfl, fun _ => trivial⟩
    isplitr
    · -- `accept` returns true
      imodintro
      iunfold replica.mset.acceptOk
      iintro %k %m %lm
      wp_start as -
      wp_auto
      iapply HΦ
      isplitr
      · itrivial
      iintro -
      iunfold replica.mset.accOk
      iright; imodintro; itrivial
    isplitr
    · -- `free` does nothing
      imodintro
      iunfold replica.mset.freeOk
      iintro %m
      wp_start as -
      wp_auto
      iapply HΦ; itrivial
    icases Hnl with (%h | Hnl)
    · ileft; ipureintro; exact h
    · iright; iapply replica.mset.ownD_ownAny $$ Hnl
  iapply HΦ
  iunfold swift.runInv
  iframe Hd Hs Hrl Hrun Hseq Hdr Hds
  iunfold swift.runFields
  iexists t, fq, rc, nl', b, ppsl, pp
  iframe
  isplitl [Hnl']
  · iunfold swift.nlSet; iright
    isimp only [swift.nlQ, swift.nlHd]
    iexact Hnl'
  isplitr
  · ipureintro; exact Hpp
  ipureintro; intro _; exact hlead

end proof

end Perennial.github_com.imdea_software.swiftpaxos

end
