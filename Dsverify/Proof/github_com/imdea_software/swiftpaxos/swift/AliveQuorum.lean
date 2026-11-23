/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AliveQuorum.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.aliveQuorumBallot(b)` (swift.go, F1/R-Q1; round 25, sv-swc): the run loop's `recBal` arm's
callee. Safety only (the arm's post is the run loop's invariant): at most `NumAQ(r.Id) + 1`
rounds; each reads `AQ(b)` (`b ≥ 0`: the next ballot of `NextBallotOfOk` is), and for each of
its replicas (`< N`: `aqOf_ok`) `r.Alive[rid]` under `r.M` (`replica.lockInv`: `Alive` has `N`
entries).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumOk
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions]

/-- `r.aliveQuorumBallot(b)` for `b ≥ 0` (see the file header). -/
abbrev swift.Replica.aliveQuorumBallot.spec : Prop :=
  ∀ (rp rr qs : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me b : w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
      swift.fld rp go!"qs" ↦□ qs ∗ replica.quorum.isQS qs N ∗
      swift.fld rp go!"fixedMajority" ↦□ true ∗
      ⌜0 ≤ sint.Z b ∧ 1 ≤ N ∧ sint.Z b % (N : Int) = sint.Z me⌝ }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"aliveQuorumBallot")) (Val #b))
  {{ (b' : w32) (ok : Bool), RET (PairV #b' #ok);
      ⌜ok = true → 0 ≤ sint.Z b' ∧ sint.Z b' % (N : Int) = sint.Z me⌝ }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions]

set_option goose.wp.extras true

open replica.quorum

theorem swift.Replica.aliveQuorumBallot.wp_proof
    (wp_NumAQ : replica.QuorumSystem.NumAQ.spec (hG := hG))
    (wp_AQ : replica.QuorumSystem.AQ.spec (hG := hG))
    (wp_NBOk : replica.NextBallotOfOk.spec (hG := hG)) :
    swift.Replica.aliveQuorumBallot.spec (hG := hG) := by
  intro rp rr qs γ γc γm γw N me b
  wp_start as ⟨#Hrr, #Hrep, #Hqs, #Hisq, #Hfm, %Hb⟩
  ihave #Hrep2 := Hrep
  iunfold replica.isReplica at Hrep2
  icases Hrep2 with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, -, -, #HN, #Hid, -, -, -, -, -, -, -, -, -, -, -, -, #Hal, -, -, %Hlen, #HM⟩
  obtain ⟨-, hme0, hmeN, hN7⟩ := Hlen
  have hN1 := Hb.2.1
  have hme : sint.Z me < N := by simp only [sint.Z]; omega
  wp_auto
  ihave HL : (∃ (bv : w32) (tr : w64) (qa : Bool),
      "b" ∷ b_ptr ↦ bv ∗ "tries" ∷ tries_ptr ↦ tr ∗ "qa" ∷ quorumIsAlive_ptr ↦ qa ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z bv ∧ 0 ≤ sint.Z tr ∧ sint.Z tr ≤ 36 ∧
        sint.Z bv % (N : Int) = sint.Z me⌝ : IProp netDistGF)
    $$ [b tries quorumIsAlive]
  · iexists b, _, _
    iframe
    ipureintro; exact ⟨Hb.1, by decide, by decide, Hb.2.2⟩
  wp_for HL
  cases qa
  · simp only [Bool.not_false]
    wp_auto
    wp_apply (wp_NumAQ qs N me) $$ [$Hisq]
    · ipureintro; exact ⟨hme0, hme⟩
    wp_if_destruct
    · wp_apply (wp_AQ qs N bv) $$ [$Hisq] as %q #Hq
      · ipureintro; exact Hi.1
      iunfold replica.quorum.qOwn at Hq
      icases Hq with ⟨%qm, #Hqm, %Hqr⟩
      -- the range over `AQ(b)` (`aqOf N b`: replicas `< N`, `aqOf_ok`): each `Alive[rid]` under
      -- `r.M` (`lockInv`: `N` entries), `NextBallotOfOk` (`b ≥ 0` kept), `break`/`return`.
      -- The invariant carries every loop resource and `HΦ` (the body is persistent and may return).
      have htr1 : sint.Z (tr + W64 1) = sint.Z tr + 1 := by
        have : sint.Z tr ≤ 36 := Hi.2.2.1
        word
      have htr : sint.Z tr ≤ 35 := by
        have h1 := go.intoVal_inj Hif
        have h2 := of_decide_eq_true h1
        have h3 := (numAQ_pos N (sint.Z me).toNat ⟨hN1, hN7⟩ (by omega)).2
        rw [sint_W64 _ (by omega) (by omega)] at h2
        omega
      wp_func_lits
      iapply (wp_map_for_range (fun _ _ => iprop(
          (∃ (bv' : w32) (qa' : Bool) (rv : w32), b_ptr ↦ bv' ∗ quorumIsAlive_ptr ↦ qa' ∗
            rid_ptr ↦ rv ∗ ⌜0 ≤ sint.Z bv' ∧ sint.Z bv' % (N : Int) = sint.Z me⌝) ∗
          tries_ptr ↦ tr ∗ «$res0_ptr» ↦ Perennial.zero_val w32 ∗
          «$res1_ptr» ↦ Perennial.zero_val Bool ∗ r_ptr ↦ rp ∗
          (∀ b' ok, ⌜ok = true → 0 ≤ sint.Z b' ∧ sint.Z b' % (N : Int) = sint.Z me⌝ -∗
            Φ (PairV #b' #ok)))) _ _ _ q qm DFrac.discard) $$ Hqm
      iintro %keys %Hkeys
      isplitl [b qa rid tries «$res0» «$res1» r HΦ]
      · iframe
        ipureintro; exact ⟨Hi.1, Hi.2.2.2⟩
      isplitr
      · imodintro
        iintro %i %key %v %Hiv ⟨⟨%bv', %qa', %rv, b, qa, rid, %Hbv'⟩, tries, «$res0», «$res1», r, HΦ⟩
        obtain ⟨-, hv⟩ := Hiv
        have hkm : key ∈ (aqOf N (sint.Z bv).toNat).map w32n := by
          have h := Hqr key; rw [hv] at h
          by_cases hn : key ∈ (aqOf N (sint.Z bv).toNat).map w32n
          · exact hn
          · rw [if_neg hn] at h; cases h
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hkm
        have hxN := (aqOf_ok N _ ⟨hN1, hN7⟩).2.2.1 x hx
        have hkz : sint.Z (w32n x) = x := sint_W32 _ (by omega) (by omega)
        wp_auto
        wp_apply sync.Mutex.wp_Lock $$ [$HM] as ⟨Hlocked, HR⟩
        iunfold replica.lockInv at HR
        icases HR with ⟨%alive, %lats, Hals, Hlat, %Hl, Hpw, Hcw⟩
        ihave %Hall := ownSlice_len _ _ _ $$ Hals
        have hlen : sint.Z alsl.len = N := by
          obtain ⟨h1, h2⟩ := Hall; rw [Hl.1] at h1
          have e1 : sint.nat alsl.len = (sint.Z alsl.len).toNat := rfl
          omega
        have hxz : sint.Z (W64 (sint.Z (w32n x))) = x := by
          rw [hkz]; exact sint_W64 _ (by omega) (by omega)
        try wp_auto
        rw [hxz, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
        have hxa : x < alive.length := by omega
        wp_apply wp_load_slice_index _ _ _ _ alive[x] (by omega) $$ [Hals] as Hals
        · iframe Hals; ipureintro; simp [hxa]
        try wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hals Hlat Hpw Hcw]
        · iframe HM Hlocked
          inext; unfold replica.lockInv
          iexists alive, lats
          iframe
          ipureintro; exact Hl
        try wp_auto
        generalize (!decide (w32n x = me)) = c1
        cases c1 <;> cases ha : alive[x] <;> try wp_auto
        all_goals try (
          unfold forMapPostcondition; iright; ileft
          isplitr
          · ipureintro; rfl
          iframe; ipureintro; exact Hbv'
          done)
        -- a replica of `AQ(b)` other than this one is not alive: the next ballot
        wp_apply (wp_NBOk me bv' N) as %nb %ok %Hok
        · ipureintro; exact ⟨hN1, hN7, hme0, hme⟩
        cases ok
        · -- `return b, false`
          wp_auto
          unfold forMapPostcondition; iright; iright; iright
          iexists _
          isplitr
          · ipureintro; rfl
          iintro -
          wp_for_post
          try wp_auto
          iapply HΦ; ipureintro; intro h; cases h
        · -- `b = nb; quorumIsAlive = false; break`
          wp_auto
          unfold forMapPostcondition; iright; iright; ileft
          isplitr
          · ipureintro; rfl
          iintro -
          wp_for_post
          try wp_auto
          iframe
          iexists _, _, _
          iframe
          ipureintro; exact ⟨(Hok rfl).1, by omega, by omega, (Hok rfl).2.2⟩
      · iintro ⟨⟨%bv', %qa', %rv, b, qa, rid, %Hbv'⟩, tries, «$res0», «$res1», r, HΦ⟩ #Hqm
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        exact ⟨Hbv'.1, by omega, by omega, Hbv'.2⟩
    · rw [if_neg (fun h => Hif (by rw [h]))]
      wp_auto
      iapply HΦ; ipureintro; intro _; exact ⟨Hi.1, Hi.2.2.2⟩
  · simp only [Bool.not_true]
    wp_auto
    rw [if_neg (by
      intro h
      have h' := of_decide_eq_true h
      have := go.intoVal_inj h'; simp at this)]
    rw [if_pos (decide_eq_true rfl)]
    wp_auto
    iapply HΦ; ipureintro; intro _; exact ⟨Hi.1, Hi.2.2.2⟩

end proof

end Perennial.github_com.imdea_software.swiftpaxos

end
