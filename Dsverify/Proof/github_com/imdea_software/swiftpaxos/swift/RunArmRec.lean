/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunArmRec.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's `recBal` arm (round 25, sv-swc): `r.recoveryBallot(nb)` over `swift.runInv`
(RunInvD.lean). Safety only (the arm's post is the invariant): it reads the run loop's quarter of
`ballot`, the replica's `N`/`Id`, the quorum system `qs`; its callees `MaxBallot`,
`QuorumSystem.SameHigherOk`, `NextBallotOfOk` (Proof/replica/QuorumOk.lean) give a ballot in
`[0, MaxBallot(N)]` when `ok`, which `aliveQuorumBallot` (AliveQuorum.lean) needs (`b ≥ 0`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunInvD
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AliveQuorum

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- The receiver's resources (persistent) in `runLoopCtx`. -/
theorem swift.runLoopCtx_rcvr (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runLoopCtx rp γ γc γm x ⊢
      swift.rcvrRes rp γc γm ∗ swift.fld rp go!"fixedMajority" ↦□ true := by
  iintro H
  iunfold swift.runLoopCtx at H
  icases H with ⟨%s, %b, %γs, %sq, %hsl, %fr, %pl, %sam, %csv, %n, #Hr, -, -, -, -, -, -, -, -, -,
    #Hfm, -⟩
  iframe Hr Hfm

/-- D56 N1-c: an own ballot (`swift.ownBallot`) at the replica's `N` and `Id`. -/
theorem swift.ownBallot_val (rp rr : Loc) (N : Nat) (me b : w32) (hN : N ≤ 7) :
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"N" ↦□ (W64 N) ∗
      replica.fld rr go!"Id" ↦□ me ∗ swift.ownBallot rp b ⊢
      ⌜0 ≤ sint.Z b ∧ sint.Z b % (N : Int) = sint.Z me⌝ := by
  iintro ⟨#H1, #H2, #H3, Hob⟩
  iunfold swift.ownBallot at Hob
  icases Hob with ⟨%rr2, %N2, %me2, #F1, #F2, #F3, %Hb⟩
  ihave %e1 : ⌜rr = rr2⌝ $$ [H1 F1]
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ H1 F1
  subst e1
  ihave %e2 : ⌜(W64 N : w64) = W64 N2⌝ $$ [H2 F2]
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ H2 F2
  ihave %e3 : ⌜me = me2⌝ $$ [H3 F3]
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ H3 F3
  subst e3
  have hNN : N = N2 := by
    have h1 := congrArg (fun w : w64 => w.toNat) e2
    have : N2 ≤ 7 := Hb.2.1
    rw [show (W64 (N : Int)).toNat = N by word, show (W64 (N2 : Int)).toNat = N2 by word] at h1
    exact h1
  subst hNN
  ipureintro; exact ⟨Hb.2.2.1, Hb.2.2.2⟩

/-- An own ballot from the replica's `N` and `Id`. -/
theorem swift.ownBallot_intro (rp rr : Loc) (N : Nat) (me b : w32) (hN : 1 ≤ N ∧ N ≤ 7)
    (hb : 0 ≤ sint.Z b ∧ sint.Z b % (N : Int) = sint.Z me) :
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"N" ↦□ (W64 N) ∗
      replica.fld rr go!"Id" ↦□ me ⊢ swift.ownBallot rp b := by
  iintro ⟨#H1, #H2, #H3⟩
  iunfold swift.ownBallot
  iexists rr, N, me
  iframe H1 H2 H3
  ipureintro; exact ⟨hN.1, hN.2, hb.1, hb.2⟩

/-- The leader of an own ballot is the replica (`b mod N = Id`). -/
theorem swift.leaderOf_emod {N : Nat} {b me : w32} (h0 : 0 ≤ sint.Z b) (hm : 0 ≤ sint.Z me)
    (hN : 1 ≤ N) (h : sint.Z b % (N : Int) = sint.Z me) : sp.leaderOf N (sp.bal b) = sp.rid me := by
  unfold sp.leaderOf sp.bal sp.rid
  show (sint.Z b).toNat % N = (sint.Z me).toNat
  rw [← h, Int.toNat_emod h0 (by omega)]
  simp

end lemmas

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

set_option goose.wp.extras true

open replica.quorum

/-- **The `recBal` arm** (see the file header). -/
theorem swift.runArm_recBal (wp_Max : replica.MaxBallot.spec (hG := hG))
    (wp_SH : replica.QuorumSystem.SameHigherOk.spec (hG := hG))
    (wp_NB : replica.NextBallotOfOk.spec (hG := hG))
    (wp_alive : swift.Replica.aliveQuorumBallot.spec (hG := hG))
    (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (nb : w32) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗ swift.recoverOk rp nb }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"recoveryBallot")) (Val #nb))
    {{ (b : w32) (ok : Bool), RET (PairV #b #ok); swift.runInv rp γ γc γm x ∗
        (⌜ok = true⌝ -∗ swift.ownBallot rp b) }} := by
  wp_start as ⟨HI, #Hrok⟩
  ihave ⟨#Hctx, HI⟩ := BI.persistent_entails_right (swift.runInv_ctx rp γ γc γm x) $$ HI
  iunfold swift.runInv at HI
  icases HI with ⟨#Hd, Hs, Hrl, ⟨%ld, %v, %M, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
  iunfold swift.runCtxD at Hctx
  icases Hctx with ⟨%rr, %me, %fr, %l', %dm, #Hrr, #Hrep, %Hids, -, -, -, -, -, -, -⟩
  ihave #Hrep2 := Hrep
  iunfold replica.isReplica at Hrep2
  icases Hrep2 with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, -, -, #HN, #Hid, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %Hlen, -⟩
  -- the quorum system (`rcvrRes`, its `N` the replica's)
  ihave ⟨⟨#Hrcvr, #Hfm⟩, Hrl⟩ := BI.persistent_entails_right (swift.runLoopCtx_rcvr rp γ γc γm x) $$ Hrl
  iunfold swift.rcvrRes at Hrcvr
  icases Hrcvr with ⟨%rr', %N', %fr3, %l3, %me', %dm', %qs, %rc, %γrc, %γdl', #FR', #FN', -, -,
    %Hn', -, -, -, #Fqs, #Hqs, -⟩
  ihave %Hrr' : ⌜rr = rr'⌝ $$ [Hrr FR']
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ Hrr FR'
  subst Hrr'
  ihave %HNN : ⌜(W64 x.N : w64) = W64 N'⌝ $$ [FN' HN]
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ HN FN'
  have hNN : x.N = N' := by
    have h1 := congrArg (fun w : w64 => w.toNat) HNN
    have : N' ≤ 7 := Hn'.2.1
    have : x.N ≤ 7 := Hids.2.2.2.2.1
    rw [show (W64 (N' : Int)).toNat = N' by word, show (W64 (x.N : Int)).toNat = x.N by word] at h1
    exact h1
  subst hNN
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hrest⟩
  ihave Hback : (typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) -∗
      swift.runInv rp γ γc γm x) $$ [Hd Hs Hrl Hrest Hseq Hdr Hrf Hpd Hds]
  · iintro Hbal
    iunfold swift.runInv
    iframe Hd Hs Hrl Hseq Hdr Hrf Hds
    iexists ld, v, M, bs, hd, w
    isplitr [Hpd]
    · iunfold swift.runSt; iframe
    · iframe Hpd; ipureintro; exact Hn
  have hN1 : 1 ≤ x.N ∧ x.N ≤ 7 := ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩
  have hme : 0 ≤ sint.Z me ∧ sint.Z me < x.N := ⟨Hlen.2.1, Hlen.2.2.1⟩
  -- D56 N1-c: the channel's value is `-1` or an own ballot
  ihave %Hnb : ⌜sint.Z nb = -1 ∨ (0 ≤ sint.Z nb ∧ sint.Z nb % (x.N : Int) = sint.Z me)⌝ $$ []
  · iunfold swift.recoverOk at Hrok
    icases Hrok with (%h | #Hob)
    · ipureintro; exact Or.inl h
    · ihave %h := swift.ownBallot_val rp rr x.N me nb hN1.2 $$ [Hrr HN Hid Hob]
      · iframe #
      ipureintro; exact Or.inr h
  ihave #Hown : (∀ b : w32, ⌜0 ≤ sint.Z b ∧ sint.Z b % (x.N : Int) = sint.Z me⌝ -∗
      swift.ownBallot rp b) $$ []
  · iintro %b %hb
    iapply swift.ownBallot_intro rp rr x.N me b hN1 hb
    iframe #
  wp_auto
  generalize hc : (!decide (nb = W32 (-1))) = c
  cases c
  · -- `newBallot == -1`: the next of this replica's ballots
    wp_auto
    wp_apply (wp_NB me v.ballot x.N) as %b' %ok' %Hok'
    · ipureintro; exact ⟨hN1.1, hN1.2, hme.1, hme.2⟩
    cases ok'
    · wp_auto
      iapply HΦ
      isplitl [Hbal Hback]
      · iapply Hback $$ Hbal
      iintro %h; cases h
    · wp_auto
      wp_apply (wp_alive rp rr qs γ γc γm x.γw x.N me b') $$ [] as %b2 %ok2 %Hal
      · iframe Hrr Hrep Fqs Hqs Hfm
        ipureintro; exact ⟨(Hok' rfl).1, hN1.1, (Hok' rfl).2.2⟩
      iapply HΦ
      isplitl [Hbal Hback]
      · iapply Hback $$ Hbal
      iintro %h
      iapply Hown; ipureintro; exact Hal h
  · -- an own ballot (D56 N1-c: the channel's value is not `-1`)
    have hnb' : 0 ≤ sint.Z nb ∧ sint.Z nb % (x.N : Int) = sint.Z me := by
      rcases Hnb with h | h
      · exfalso
        have : nb = W32 (-1) := by
          apply BitVec.eq_of_toInt_eq; show sint.Z nb = sint.Z (W32 (-1)); rw [h]; rfl
        simp [this] at hc
      · exact h
    wp_auto
    wp_join iprop(∃ (bv : w32) (okv : Bool), b_ptr ↦ bv ∗ ok_ptr ↦ okv ∗ r_ptr ↦ rp ∗
        newBallot_ptr ↦ nb ∗
        typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) ∗
        ⌜okv = true → 0 ≤ sint.Z bv ∧ sint.Z bv % (x.N : Int) = sint.Z me⌝)
      with [b ok r newBallot Hbal] as ⟨%bv, %okv, b, ok, r, newBallot, Hbal, %Hbv⟩
    · wp_if_destruct
      · wp_apply (wp_Max x.N)
        · ipureintro; exact hN1
        wp_join_done
        iexists _, _
        iframe
        ipureintro; intro _; exact hnb'
      · wp_join_done
        iexists _, _
        iframe
        ipureintro; intro h; cases h
    · wp_apply (wp_SH qs x.N nb v.ballot) $$ [$Hqs] as %b' %ok' %Hok'
      wp_join_done
      iexists _, _
      iframe
      ipureintro; intro h; exact ⟨(Hok' h).1, (Hok' h).2.2.trans hnb'.2⟩
    cases okv
    · wp_auto
      iapply HΦ
      isplitl [Hbal Hback]
      · iapply Hback $$ Hbal
      iintro %h; cases h
    · wp_auto
      wp_apply (wp_alive rp rr qs γ γc γm x.γw x.N me bv) $$ [] as %b2 %ok2 %Hal
      · iframe Hrr Hrep Fqs Hqs Hfm
        ipureintro; exact ⟨(Hbv rfl).1, hN1.1, (Hbv rfl).2⟩
      iapply HΦ
      isplitl [Hbal Hback]
      · iapply Hback $$ Hbal
      iintro %h
      iapply Hown; ipureintro; exact Hal h

end proof

end Perennial.github_com.imdea_software.swiftpaxos

end
