/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__restoreSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).restoreSnapshot`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__restoreSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__tryRestoreSingleSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastApplied
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration
public import Perennial.Proof.sync
public import Dsverify.Proof.github_com.hashicorp.raft.core.LastLock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem restore_CIdx_agree (γ : gprot.GNames) (k : Nat) (e1 e2 : Entry) :
    gprot.CIdx (GF := GF) γ k e1 ∗ gprot.CIdx γ k e2 ⊢ ⌜e1 = e2⌝ := by
  unfold gprot.CIdx
  iintro ⟨⟨_, #H1⟩, ⟨_, #H2⟩⟩
  iapply mono_list_idx_agree γ.C (k - 1) e1 e2 $$ H1 H2

theorem github_com.hashicorp.raft.Raft.restoreSnapshot.wp_proof
    (wp_tryRestoreSingleSnapshot :
      github_com.hashicorp.raft.Raft.tryRestoreSingleSnapshot.spec (GF := GF) (hG := hG))
    (wp_setLastApplied : github_com.hashicorp.raft.raftState.setLastApplied.spec (GF := GF) (hG := hG))
    (wp_setCommittedConfiguration :
      github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec (GF := GF) (hG := hG))
    (wp_setLatestConfiguration :
      github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.restoreSnapshot.spec (GF := GF) (hG := hG) := by
  intro r γ i rc c x fx eof lat P li lt c0 l0 i0 li0 p0 tid
  wp_start as ⟨#Hconf, %Hnsr, #Hsnaps, #Hsn, #Heof, #Hfsml, #Hfsm, HP, #Hacc, #Happc, Happ,
    #Hll, Hgll, Hllb, Hcfgs, Hlp, Hfo, Htok⟩
  wp_auto
  ihave #Hsn' := Hsn
  iunfold isSnapStore at Hsn'
  icases Hsn' with ⟨-, #HList, -⟩
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HList $$ Htok
  ihave Hl := Hacc $$ HP
  iapply ncfupd_wand
  isplitl [Hl]
  · iexact Hl
  iintro Hl
  inext
  icases Hl with ⟨%old, Hown, %Hold, Hcl⟩
  subst Hold
  iexists _
  iframe Hown
  iintro Hown
  imod Hcl $$ Hown with ⟨HP, #Hlat⟩
  imodintro
  iintro %sl %ps Hsl Hps Htok
  wp_auto
  rcases old with _ | ⟨m, b⟩
  · -- no snapshot: nothing restored
    icases Hps with %Hps
    subst Hps
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    wp_for
    wp_if_destruct
    · exfalso; simp at Hsll; word
    wp_if_destruct
    · exfalso; simp at Hsll; word
    iapply HΦ
    iframe
    unfold latFacts; itrivial
  · skip
    icases Hps with ⟨%mp, %Hps, Hmp⟩
    subst Hps
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    wp_for
    wp_if_destruct
    rotate_left
    · exfalso; simp at Hsll
      have : ¬ (sint.Z (W64 0) < sint.Z sl.len) := fun h => Hif h
      word
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by word, Hif⟩)]
    wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) [mp] (DFrac.own 1) mp (by word)) $$ [$Hsl] as Hsl
    · ipureintro; simp
    ihave #Hlat0 := Hlat
    iunfold latFacts at Hlat0
    icases Hlat0 with ⟨#HsP, ⟨%e, #HC, %He⟩, #Hdl, ⟨%ss, #Hcv, #Hscfg⟩, %Hvp⟩
    wp_apply (wp_tryRestoreSingleSnapshot r c x fx rc.ownSS eof (snapWin γ rc i) γ i rc.fsmOwn rc.respP
      rc.snapP mp m b P 0 tid) $$ [$Hmp $HP $Hfo $Htok] as ⟨Hmp, HP, Htok, %k0, %res, Hfo, %Hk0, #Hnc, Hres⟩
    · iframe #
      isplitr
      · ipureintro; exact Hnsr
      isplitr
      · iintro HP
        ihave Hl := Hacc $$ HP
        iapply ncfupd_wand
        isplitl [Hl]
        · iexact Hl
        iintro Hl
        inext
        icases Hl with ⟨%old, Hown, %Hold, Hcl⟩
        iexists old
        iframe Hown
        isplitr
        · ipureintro; exact Hold
        iintro Hown
        imod Hcl $$ Hown with ⟨HP, -⟩
        imodintro; iexact HP
      ipureintro
      exact Nat.zero_le _
    -- setLastApplied(m.Index)
    wp_bind (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLastApplied")) _)
    iapply (wp_setLastApplied r rc m.Index') $$ [$Hpkg $Happc]
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists 0
    iframe Happ
    isplitr
    · ipureintro; omega
    iintro Happ
    imod Hmask with -
    imodintro
    wp_auto
    -- setLastSnapshot(m.Index, m.Term), inlined
    rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"setLastSnapshot")]
    wp_call
    rw [MethodUnfold.method_unfold (t := go.GoType.PointerType raftState.ty) (m := go!"setLastSnapshot")]
    wp_call
    wp_auto
    wp_apply (sync.Mutex.wp_Lock _ (lastLockInv r γ rc i)) $$ [$Hll] as ⟨Hown, HL⟩
    iunfold lastLockInv at HL
    icases HL with ⟨%li1, %lt1, %si1, %st1, Hx, Hy, Hsi, Hst, Hg', #Hsn0, Hb⟩
    icases Hb with (Hb | Hb)
    · icombine Hb Hllb gives %Hag; cases Hag.2
    icombine Hb Hllb gives %Hag
    obtain ⟨-, Hag⟩ := Hag
    simp only [Option.some.injEq, Prod.mk.injEq] at Hag
    obtain ⟨h1, h2, h3, h4⟩ := Hag
    subst li1 lt1 si1 st1
    imod dghostVar_update_halves (some (li, lt, m.Index', m.Term')) _ _ _ $$ Hb Hllb with ⟨Hb, Hllb⟩
    wp_auto
    imod ghostVar_update_halves (if uint.nat li < uint.nat m.Index' then (uint.nat m.Index', uint.nat m.Term')
        else (uint.nat li, uint.nat lt)) _ _ _ $$ Hgll Hg' with ⟨Hgll, Hg'⟩
    ihave #HappLb := monoNatLbOwn_get _ _ _ $$ Happ
    wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hll Hown Hx Hy Hsi Hst Hg' Hb]
    · iframe #; iframe
      inext
      iunfold lastLockInv
      iexists li, lt, m.Index', m.Term'
      iframe
      iright
      iexists e
      iframe #
      isplitr
      · ipureintro; exact He.1
      unfold applLb; iexact HappLb
    rw [Hvp.1]
    wp_auto
    wp_apply wp_setCommittedConfiguration $$ [$Hcfgs] as Hcfgs
    have hslc := wp_setLatestConfiguration true r γ
    simp only [↓reduceIte] at hslc
    unfold cfgVal
    icases Hcv with ⟨#Hss, %Hssok⟩
    wp_apply hslc $$ [$Hcfgs $Hlp $Hss] as ⟨Hcfgs, -, %pc, %cfg', Hlp, #Hpc, Hss2⟩
    wp_for_post
    iapply HΦ
    iframe
    iframe #
    ipureintro; exact Hk0

end proof

end Perennial
