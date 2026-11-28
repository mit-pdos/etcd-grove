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
  intro r γ i rc c x fx eof lat P n t c0 l0 i0 li0 p0 tid
  wp_start as ⟨#Hconf, %Hnsr, #Hsnaps, #Hsn, #Heof, #Hfsml, #Hfsm, HP, #Hacc, #Hlat, #Happc, Happ,
    #Hll, Hgll, Hcfgs, Hlp, Hfo, Htok⟩
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
  imod Hcl $$ Hown with HP
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
  · skip
    icases Hps with ⟨%mp, %Hps, Hmp⟩
    subst Hps
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    wp_for
    wp_if_destruct
    rotate_left
    · exfalso; simp at Hsll; word
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by word, Hif⟩)]
    wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) [mp] (DFrac.own 1) mp (by word)) $$ [$Hsl] as Hsl
    · ipureintro; simp
    unfold latFacts
    icases Hlat with ⟨#HsP, ⟨%e, #HC, %He⟩, #Hdl, ⟨%ss, #Hcv, #Hscfg⟩, %Hvp⟩
    wp_apply (wp_tryRestoreSingleSnapshot r c x fx rc.ownSS eof (snapWin γ rc i) γ i rc.fsmOwn rc.respP
      rc.snapP mp m b P 0 tid) $$ [$Hmp $HP $Hfo $Htok] as ⟨Hmp, HP, Htok, %k0, %res, Hfo, %Hk0, #Hnc, Hres⟩
    · iframe #
      ipureintro
      exact ⟨Hnsr, Nat.zero_le _⟩
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
    icases HL with ⟨%li0, %lt0, %si0, %st0, Hx, Hy, Hsi, Hst, Hg', #Hsn0⟩
    icombine Hgll Hg' gives %Hag
    have Hag := Hag.2
    -- the new effective last entry is the spec's
    ihave %hg : (⌜(if uint.nat li0 < uint.nat m.Index' then (uint.nat m.Index', uint.nat m.Term')
        else (uint.nat li0, uint.nat lt0)) =
        (if n < uint.nat m.Index' then (uint.nat m.Index', uint.nat m.Term') else (n, t))⌝ : IProp GF) $$ [Happ]
    · icases Hsn0 with (%h0 | ⟨%e0, #HC0, %He0, #Hlb0, -⟩)
      · subst h0
        simp only [show uint.nat (W64 0) = 0 from rfl, Nat.not_lt_zero, ite_false] at Hag
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hag
        ipureintro; rfl
      · ihave %hle := applLb_le rc (1 : Qp).half (uint.nat m.Index') (uint.nat si0) $$ [Happ Hlb0]
        · iframe; iexact Hlb0
        by_cases hl : uint.nat li0 < uint.nat si0
        · rw [if_pos hl] at Hag
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hag
          rw [if_pos (by omega : uint.nat li0 < uint.nat m.Index')]
          by_cases hs : uint.nat si0 < uint.nat m.Index'
          · rw [if_pos hs]; ipureintro; rfl
          · have hs' : uint.nat si0 = uint.nat m.Index' := by omega
            rw [if_neg hs]
            have hsw : si0 = m.Index' := by apply BitVec.eq_of_toNat_eq; simpa using hs'
            subst hsw
            ihave %hee : (⌜e0 = e⌝ : IProp GF) $$ []
            · iapply (restore_CIdx_agree γ (uint.nat m.Index') e0 e)
              isplitr
              · iexact HC0
              · iexact HC
            subst hee
            ipureintro
            rw [← He0, He.1]
        · rw [if_neg hl] at Hag
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hag
          ipureintro; rfl
    wp_auto
    imod ghostVar_update_halves (if uint.nat li0 < uint.nat m.Index' then (uint.nat m.Index', uint.nat m.Term')
        else (uint.nat li0, uint.nat lt0)) _ _ _ $$ Hgll Hg' with ⟨Hgll, Hg'⟩
    ihave #HappLb := monoNatLbOwn_get _ _ _ $$ Happ
    wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hll Hown Hx Hy Hsi Hst Hg']
    · iframe #; iframe
      inext
      iunfold lastLockInv
      iexists li0, lt0, m.Index', m.Term'
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
    rw [← hg]
    iframe
    iframe #
    ipureintro; exact Hk0

end proof

end Perennial
