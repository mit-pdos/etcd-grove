/-
The shared mode of the tree: `open(2)` of a directory, read-only (`wp_osOpenDirS'`): a shared
directory fd, which holds nothing. `TreeShared.lean` states the spec and takes its proof from here.
Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedStep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The shared coherence with a directory fd set (added, or its read moved on). -/
theorem treeCohS_setDfd {st : OsState} {s0 : Nat} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc : GMap Nat (Nat × Qp)} (hc : TreeCohS st s0 Γdf Γc) {fd : w64} {df' : OsDirFd}
    {x : Ino × DirPhS} (hino : x.1 = df'.ino) (hph : PhOkS (setDfd st fd df') x.1 x.2 df'.rd) :
    TreeCohS (setDfd st fd df') s0 (<[fd := x]> Γdf) Γc := by
  refine ⟨hc.starts, hc.pss, hc.dox, hc.valid, hc.s0le, fun fd' => ?_, fun fd' x' df hx hdf => ?_,
    hc.calls, hc.callsLe, hc.whole, hc.after⟩
  · show ((<[fd := x]> Γdf) !! fd').map (·.1) = ((<[fd := df']> st.proc.dfds) !! fd').map (·.ino)
    rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]; split
    · simp [hino]
    · exact hc.fds fd'
  · have hdf' : (<[fd := df']> st.proc.dfds) !! fd' = some df := hdf
    rw [GMap.lookup_insert_eq_iff] at hx hdf'
    split at hx
    · rw [if_pos ‹_›] at hdf'; cases hx; cases hdf'; exact hph
    · rw [if_neg ‹_›] at hdf'; exact (hc.ph fd' x' df hx hdf').congr rfl rfl

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem wp_osOpenDirS' (R : Roots) (p : GoString) (j : Ino) (dq : DFrac) (k s0 : Nat) (q : Qp)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R p dq j -∗
      osCallS (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗ osCallPerm (L := L) q -∗
        osPathS (L := L) R p dq j -∗ (⌜e = 0⌝ -∗ osDirFdS (L := L) fd j .idle) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#p) (#flRO))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hk HΦ
  iapply wp_fs_stepM "Open" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  icases Hm with (Hm | Hm)
  · iexfalso; iapply legacy_callS_excl st k s0 q $$ Hk Hm
  unfold treeShared
  icases Hm with ⟨%V0, %s1, %Γdf, %Γc, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  icases osPathS_lookup hR hcoh.2 p dq j $$ HAn Hp with %hl
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osCallS
  icases gAuth_lookup _ _ _ _ _ _ $$ Hacs Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := by
    have := hc.calls k; rw [hk] at this; exact this.symm
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcr : decide ((flRO.toNat / O_CREAT) % 2 = 1) = false := by decide
  have htr : decide ((flRO.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flRO.toNat % 4 = O_RDONLY := by decide
  have hl0 : (st.metaEnd k).lookup p = some (.dir j) := hl
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_metaEnd st k) Hag
    exact ⟨_, h, _, ⟨p, flRO, k, s0, rfl, treePath_of_lookup hl, flRO_ok, hcall,
      ⟨fun h => (Bool.false_ne_true (htr.symm.trans h)).elim,
        .inr ⟨1, by decide, rfl, .inl rfl⟩⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨p', fl, k', s', hv, -, -, hk', hres⟩ := Hst
  injection hv with hv1 hv2
  have hkk : k' = k := by injection hv1 with h1; exact (extVal_inj h1).symm
  subst hkk
  injection hv2 with hv3 hv4
  cases go.intoVal_inj hv3; cases go.intoVal_inj hv4
  rw [hcall] at hk'; cases hk'
  simp only [hcr, htr, hacc, Bool.false_eq_true, ↓reduceIte] at hres
  -- the call's fraction back
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : Nat × Qp) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own x.2) ()) hk).1 $$ Hcr
    with ⟨Hq, Hcr⟩
  imod gAuth_delete _ _ _ _ _ $$ Hacs Hk with Hacs
  obtain ⟨-, hres⟩ := hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · unfold OpenEffect at heff
    rw [hl0] at heff
    obtain ⟨-, -, -, hst1, rfl⟩ := heff
    subst st1
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hΓ : Γdf !! fd = none := by
      have := hc.fds fd; rw [hdfn] at this
      cases h0 : Γdf !! fd with
      | none => rfl
      | some x => rw [h0] at this; cases this
    imod gAuth_insert _ _ _ fd ((j, DirPhS.idle) : Ino × DirPhS) hΓ $$ Hadfs with ⟨Hadfs, Hfd⟩
    have hst'' : st' = setDfd (st.metaEnd k') fd ⟨j, .idle⟩ := hst
    subst hst''
    have hs : FilesSame st (setDfd (st.metaEnd k') fd ⟨j, .idle⟩) := ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hw' := fsTreeWf_setDfd (fsTreeWf_metaEnd hw k') (fd := fd) (df' := ⟨j, .idle⟩) hfdn
      (mem_of_lookup_dir hw hl)
    have hc' : TreeCohS (setDfd (st.metaEnd k') fd ⟨j, .idle⟩) s1
        (<[fd := ((j, DirPhS.idle) : Ino × DirPhS)]> Γdf) (GMap.delete k' Γc) :=
      treeCohS_setDfd (treeCohS_metaEnd hc k') rfl trivial
    imod osWorld_filesSame (st := st) (st' := setDfd (st.metaEnd k') fd ⟨j, .idle⟩) hs Hr Hfr
      $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st)
          (st' := setDfd (st.metaEnd k') fd ⟨j, .idle⟩) (commitGrows_of_eq rfl) $$ Hcm
      iright
      simp only [setDfd, OsState.metaEnd, OsState.setProc]
      try unfold treeShared
      iexists V0, s1, _, GMap.delete k' Γc
      iframe
      ipureintro; exact ⟨hw', hc'⟩
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfd0⟩) [Hq] Hp
    · unfold osCallPerm; iexact Hq
    iintro -
    unfold osDirFdS; iexact Hfd
  · have hst' : st' = st.metaEnd k' := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold OpenEffect at heff; rw [hl0] at heff; exact heff.2.2.2.1
    subst hst'
    imod osWorld_filesSame (st := st) (st' := st.metaEnd k') (filesSame_metaEnd st k') Hr Hfr
      $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st.metaEnd k')
          (commitGrows_of_eq rfl) $$ Hcm
      iright
      simp only [OsState.metaEnd]
      try unfold treeShared
      iexists V0, s1, Γdf, GMap.delete k' Γc
      iframe
      ipureintro; exact ⟨fsTreeWf_metaEnd hw k', treeCohS_metaEnd hc k'⟩
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩) [Hq] Hp
    · unfold osCallPerm; iexact Hq
    iintro %he0
    exact absurd he0 he

end specs

end Fs
end Perennial

end
