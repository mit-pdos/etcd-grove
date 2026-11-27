/-
The shared mode of the tree: the steps on a shared directory fd that hold no claim (`FdKind`,
`DirClose`, `DirSync`). `TreeShared.lean` states the specs and takes their proofs from here.
Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedClaims

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The shared coherence with a directory fd gone. -/
theorem treeCohS_delDfd {st : OsState} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st Γdf Γc Γg) (fd : w64) :
    TreeCohS (delDfd st fd) (GMap.delete fd Γdf) Γc Γg := by
  refine ⟨hc.starts, hc.pss, hc.rc.elim (fun ρ h => ⟨ρ, h.1.congr rfl rfl rfl, h.2.congr rfl rfl⟩), hc.valid, fun fd' => ?_, fun fd' x df hx hdf => ?_,
    hc.calls, hc.callsLe, hc.gcalls, hc.gdisj,
    hc.cover⟩
  · show (GMap.delete fd Γdf !! fd').map (·.1) = (GMap.delete fd st.proc.dfds !! fd').map (·.ino)
    rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]
    split
    · rfl
    · exact hc.fds fd'
  · have hdf' : (GMap.delete fd st.proc.dfds) !! fd' = some df := hdf
    rw [GMap.lookup_delete_iff] at hx hdf'
    split at hx
    · cases hx
    · rw [if_neg ‹_›] at hdf'
      exact (hc.ph fd' x df hx hdf').congr rfl rfl

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- A shared directory fd is one of the state's, on its directory. -/
theorem dfdS_lookup {st : OsState} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st Γdf Γc Γg) {fd : w64} {j : Ino} {ph : DirPhS}
    (h : Γdf !! fd = some (j, ph)) : ∃ df, st.proc.dfds !! fd = some df ∧ df.ino = j := by
  have := hc.fds fd; rw [h] at this
  cases h0 : st.proc.dfds !! fd with
  | none => rw [h0] at this; cases this
  | some df => rw [h0] at this; simp only [Option.map_some, Option.some.injEq] at this
               exact ⟨df, rfl, this.symm⟩

theorem wp_osFdKindDirS' (fd : w64) (j : Ino) (ph : DirPhS) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFdS (L := L) fd j ph -∗ (osDirFdS (L := L) fd j ph -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp fsExt.name "FdKind" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepM "FdKind" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  icases (treeCtx_eq _ _).1 $$ Ht with ⟨Ht, Hcm⟩
  unfold treeCtxT
  icases Ht with ⟨%Γdf, %Γc, %Γg, %hns, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osDirFdS
  icases gFdElem_lookup _ _ _ _ _ _ $$ Hadfs Hfd with %Hfl
  obtain ⟨df, hdf, -⟩ := dfdS_lookup hc Hfl
  have hnf : st.proc.fds !! fd = none := by
    cases h0 : st.proc.fds !! fd with
    | none => rfl
    | some d => have := hw.disj fd (by rw [h0]; simp); rw [hdf] at this; cases this
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨fd, rfl, rfl, .inr (.inl ⟨hnf, ⟨df, hdf⟩, rfl⟩)⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', hv, hst, hres⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  rcases hres with ⟨⟨d, hd⟩, -⟩ | ⟨-, -, rfl⟩ | ⟨-, hd, -⟩
  · rw [hnf] at hd; cases hd
  rotate_left
  · rw [hdf] at hd; cases hd
  imod osWorld_filesSame (st := st) (st' := st) (filesSame_refl st) Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
  · iapply (treeCtx_eq _ _).2
    iframe Hcm
    try unfold treeCtxT
    iexists Γdf, Γc, Γg
    try unfold callResS
    iframe
    ipureintro; exact ⟨hw, hc⟩
  iapply wp_value'
  iapply HΦ; (try unfold osDirFdS); iexact Hfd

theorem wp_osDirCloseS' (fd : w64) (j : Ino) (ph : DirPhS) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFdS (L := L) fd j ph -∗ (∀ e : w64, Φ (#e)) -∗
      WP (ExternalOp fsExt.name "DirClose" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepM "DirClose" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  icases (treeCtx_eq _ _).1 $$ Ht with ⟨Ht, Hcm⟩
  unfold treeCtxT
  icases Ht with ⟨%Γdf, %Γc, %Γg, %hns, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osDirFdS
  icases gFdElem_lookup _ _ _ _ _ _ $$ Hadfs Hfd with %Hfl
  obtain ⟨df, hdf, -⟩ := dfdS_lookup hc Hfl
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hs : FilesSame st (delDfd st fd) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 hs Hag
    exact ⟨_, h, _, ⟨fd, 0, df, rfl, hdf, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', e, df', hv, -, hst, rfl⟩ := Hst
  cases go.intoVal_inj hv
  subst hst
  imod gFdElem_delete _ _ _ _ _ $$ Hadfs Hfd with Hadfs
  imod osWorld_filesSame (st := st) (st' := delDfd st fd) hs Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
  · iapply (treeCtx_eq _ _).2
    isplitr [Hcm]
    rotate_left
    · iapply commitRes_setProc $$ Hcm
    try unfold treeCtxT
    simp only [delDfd, OsState.setProc]
    iexists GMap.delete fd Γdf, Γc, Γg
    try unfold callResS
    iframe
    ipureintro; exact ⟨fsTreeWf_delDfd hw fd, treeCohS_delDfd hc fd⟩
  iapply wp_value'
  iapply HΦ

theorem wp_osDirSyncS' (R : Roots) (fd : w64) (j : Ino) (ph : DirPhS) (n : Nat) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osDirFdS (L := L) fd j ph -∗
      osLogLb (L := L) n -∗
      (∀ e : w64, osDirFdS (L := L) fd j ph -∗ (⌜e ≠ 0⌝ ∨ osCommitLb (L := L) n) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "DirSync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hfd #Hlb HΦ
  iapply wp_fs_stepM "DirSync" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  icases (treeCtx_eq _ _).1 $$ Ht with ⟨Ht, Hcm⟩
  unfold treeCtxT
  icases Ht with ⟨%Γdf, %Γc, %Γg, %hns, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  obtain ⟨hw, hc⟩ := hns
  -- the log is at least `n` long
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨-, rfl⟩ := hVs
  unfold osLogLb
  icases (letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn_valid _ _ _ _) $$ Halen Hlb with %hn
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osDirFdS
  icases gFdElem_lookup _ _ _ _ _ _ $$ Hadfs Hfd with %Hfl
  obtain ⟨df, hdf, -⟩ := dfdS_lookup hc Hfl
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨fd, df, rfl, hdf, .inr ⟨1, by decide, rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', df', hv, -, hres⟩ := Hst
  cases go.intoVal_inj hv
  rcases hres with ⟨rfl, rfl⟩ | ⟨e, he, rfl, hst⟩
  · -- success: the whole log committed
    have hw' : FsTreeWf st.commitAll := ⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩
    have hc' : TreeCohS st.commitAll Γdf Γc Γg := hc.congr rfl rfl rfl rfl rfl
    imod osWorld_filesSame (st := st) (st' := st.commitAll) ⟨rfl, rfl, rfl, rfl, rfl⟩ Hr Hfr
      $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imod commitRes_commitAll st $$ Hcm with ⟨Hcm, #Hcl⟩
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · iapply (treeCtx_eq _ _).2
      iframe Hcm
      try unfold treeCtxT
      simp only [OsState.commitAll]
      iexists Γdf, Γc, Γg
      try unfold callResS
      iframe
      ipureintro; exact ⟨hw', hc'⟩
    iapply wp_value'
    iapply HΦ $$ %0 [Hfd]
    · (try unfold osDirFdS); iexact Hfd
    · iright; iapply osCommitLb_le n hn.2 $$ Hcl
  · -- failure: nothing changed
    subst st'
    imod osWorld_filesSame (st := st) (st' := st) (filesSame_refl st) Hr Hfr
      $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · iapply (treeCtx_eq _ _).2
      iframe Hcm
      try unfold treeCtxT
      iexists Γdf, Γc, Γg
      try unfold callResS
      iframe
      ipureintro; exact ⟨hw, hc⟩
    iapply wp_value'
    iapply HΦ $$ %e [Hfd]
    · (try unfold osDirFdS); iexact Hfd
    · ileft; ipureintro; exact he

end specs

end Fs
end Perennial

end
