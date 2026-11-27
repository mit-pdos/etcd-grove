/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__configurationChangeChIfStable.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).configurationChangeChIfStable`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__configurationChangeChIfStable
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCommitIndex
public import Dsverify.Proof.github_com.hashicorp.raft.leader.MainCfg

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft
open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `configurationChangeChIfStable` reads `commitment.startIndex` without the commitment's lock:
`isCommitment` gives it read-only (MAIN-L 2), (review T1-2) with its value `len0 + 1`. -/
theorem commitment_startIndex (γ : GNames) (i : SID) (T : Nat) (cm : Loc) :
    isCommitment γ i T cm ⊢ (∃ (si : w64) (n0 : Nat), cm.[commitment, go!"startIndex"] ↦□ si ∗
      len0Is γ T n0 ∗ ⌜uint.nat si = n0 + 1⌝ : IProp GF) := by
  unfold isCommitment
  iintro ⟨H, -⟩
  iexact H

end defs
end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

/-- (hub L1) When the channel is returned, the latest configuration is the committed one
(`mainOwnAtSt`), what `appendConfigurationEntry` needs. -/
theorem github_com.hashicorp.raft.Raft.configurationChangeChIfStable.wp_proof
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.configurationChangeChIfStable.spec (GF := GF) (hG := hG) := by
  intro r γ rc i s cm
  wp_start as ⟨#Hr, Hm, Hcm, #Hcmi⟩
  ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Hcells := isRaft_cells r γ rc i $$ Hr
  unfold raftCells
  icases Hcells with ⟨-, #HcidxC, -⟩
  ihave ⟨%ccch, %γq, #Hccf, #Hccb⟩ := isRaft_configurationChangeCh r γ rc i $$ Hr
  ihave ⟨%a, Hsrv, HlastLog, Happ, %Ha, HlogPend, #Hldr, Hrest, Hconf⟩ := mainOwnAt_lopen r γ rc i s $$ Hm
  iunfold confOwn at Hconf
  icases Hconf with ⟨%cfg, %ccfg, %cidx, %li, Hconfs, #Hcfg, #Hccfg, %Hli, #Hcmt, Hcc, %n0, #Hn0, #Hcix, #Hcl⟩
  ihave ⟨%si, %n0', #Hsi, #Hn0', %Hsin⟩ := commitment_startIndex γ i s.term cm $$ Hcmi
  ihave %Hnn := len0Is_agree γ s.term n0 n0' $$ [Hn0 Hn0']
  · iframe #
  subst Hnn
  imod srvOwn_facts γ ⊤ (by solve_ndisj) i s $$ [Hsrv] with ⟨Hsrv, -, %Hfacts⟩
  · iframe; iframe #
  wp_auto
  wp_if_destruct
  · have hcl' : cidx = li := by
      first | exact Hif.symm | exact Hif | (simp only [decide_eq_true_eq] at Hif; exact Hif.symm)
    subst hcl'
    wp_apply wp_getCommitIndex.1 $$ [$Hsrv $HInv $HcidxC] as Hsrv
    wp_if_destruct
    · have hc : n0 < s.cidx := by
        have h62 : s.cidx < 2 ^ 62 := by have := Hfacts.2.2.1; have := Hfacts.2.1; have := Hfacts.2.2.2.2.2.2.1; omega
        have : uint.nat si ≤ uint.nat (W64 (s.cidx : Int)) := by word
        have : uint.nat (W64 (s.cidx : Int)) = s.cidx := by word
        omega
      ihave #Hcl2 : (⌜uint.nat cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat cidx ≤ k⌝ : IProp GF) $$ []
      · icases Hcl with (%h | Hk)
        · ileft; ipureintro; rcases h with h | h
          · exact absurd rfl h
          · exact h
        · iright; iexact Hk
      ihave #Hst : (∃ k p : Nat, commitIs γ s.term k p ∗ ⌜lastCfgIdx s.log ≤ k⌝ : IProp GF) $$ []
      · icases Hcl2 with (%h | ⟨%k, %p, #Hk, %Hkle⟩)
        · icases Hcix with (%Hle | ⟨%k, %p, #Hk, %Hkle⟩)
          · exfalso; omega
          iexists k, p; iframe #; ipureintro; omega
        · iexists k, p; iframe #; ipureintro; omega
      iapply HΦ
      iframe Hcm
      iright
      isplitl
      rotate_left
      · isplitr; · iexists γq; iexact Hccb
        iexact Hst
      iapply mainOwnAtSt_close r γ rc i s a
      iframe Hsrv HlastLog Happ HlogPend Hrest Hldr
      isplitr; · ipureintro; exact Ha
      unfold confOwnSt
      iexists cfg, ccfg, cidx
      iframe; iframe #
      ipureintro; exact Hli.1
    · iapply HΦ
      iframe Hcm
      ileft
      isplitr; · ipureintro; rfl
      iapply mainOwnAt_lclose r γ rc i s a
      iframe Hsrv HlastLog Happ HlogPend Hrest
      iframe #
      isplitr; · ipureintro; exact Ha
      iapply confOwn_intro r γ i s a cfg ccfg cidx cidx n0 Hli
      iframe; iframe #
  iapply HΦ
  iframe Hcm
  ileft
  isplitr; · ipureintro; rfl
  iapply mainOwnAt_lclose r γ rc i s a
  iframe Hsrv HlastLog Happ HlogPend Hrest
  iframe #
  isplitr; · ipureintro; exact Ha
  iapply confOwn_intro r γ i s a cfg ccfg cidx li n0 Hli
  iframe; iframe #

  /- stage-3 proof (of wp_proof):
  :=
  fun r γ rc i s st T cm => by
  wp_start as ⟨#Hr, Hm, Hcm, #Hcmi⟩
  ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Hcells := isRaft_cells r γ rc i $$ Hr
  unfold raftCells
  icases Hcells with ⟨-, #HcidxC, -, -, -, -, -⟩
  ihave #Hch := isRaft_chans r γ rc i $$ Hr
  unfold raftChans
  icases Hch with ⟨-, -, -, -, -, -, -, -, -, #Hccc, -⟩
  unfold deadField
  icases Hccc with ⟨%ccch, #Hccf, #Hccd⟩
  unfold mainOwnAt
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %cmp, Hsrv, Hm⟩
  ihave ⟨%si, #Hsi⟩ := commitment_startIndex γ i T cm $$ Hcmi
  icases Hm with ⟨Hdur, HownS, %Hvm, HlastLog, Hst, Hldr', HlogPend, Hreg, Happ, %Ha, Hprod, Hpnd, Hcomp, %Hcmp, Hconf,
    #Hcfg, %Hccfg, #Hlch, #Hlchan, Hlown, %Hlcap⟩
  wp_auto
  wp_if_destruct
  · have hcl' : cidx = li := by
      first | exact Hif.symm | exact Hif | (simp only [decide_eq_true_eq] at Hif; exact Hif.symm)
    wp_apply wp_getCommitIndex.1 $$ [$Hsrv $HInv $HcidxC] as Hsrv
    wp_if_destruct
    · iapply HΦ
      isplitl [Hsrv Hdur HownS HlastLog Hst Hldr' HlogPend Hreg Happ Hprod Hpnd Hcomp Hconf Hlown]
      · iexists a, sst, cfg, ccfg, _, lch, γl, bs, cmp
        iframe; iframe #; ipureintro; exact ⟨Hvm, Ha, Hcmp, Hccfg, Hlcap⟩
      isplitl [Hcm]; · iexact Hcm
      iright; iexact Hccd
    · iapply HΦ
      isplitl [Hsrv Hdur HownS HlastLog Hst Hldr' HlogPend Hreg Happ Hprod Hpnd Hcomp Hconf Hlown]
      · iexists a, sst, cfg, ccfg, _, lch, γl, bs, cmp
        iframe; iframe #; ipureintro; exact ⟨Hvm, Ha, Hcmp, Hccfg, Hlcap⟩
      isplitl [Hcm]; · iexact Hcm
      ileft; ipureintro; rfl
  · iapply HΦ
    isplitl [Hsrv Hdur HownS HlastLog Hst Hldr' HlogPend Hreg Happ Hprod Hpnd Hcomp Hconf Hlown]
    · iexists a, sst, cfg, ccfg, _, lch, γl, bs, cmp
      iframe; iframe #; ipureintro; exact ⟨Hvm, Ha, Hcmp, Hccfg, Hlcap⟩
    isplitl [Hcm]; · iexact Hcm
    ileft; ipureintro; rfl
  -/

end proof

end Perennial
