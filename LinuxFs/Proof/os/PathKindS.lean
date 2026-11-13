/-
The extension's query `PathKind` in the tree's shared mode (2026-11-13, `os.MkdirAll`'s model asks
it first). Untrusted.

* `wp_osPathKindS`: `PathKind(p)` of a path of the roots `R` (a root followed by valid components,
  `PathIn`): `#1` if it is strictly below a root (`RootsTreeName`), `#0` otherwise (a root); nothing
  changes. The roots are `R` in the shared mode (the shared invariant's `γs` element against
  `treeShared`'s authority); the legacy mode is excluded (its `γs` authority is empty).
* `wp_osPathKindAboveS`: `PathKind(p)` of a strict ancestor of a root of `R` (`RootsAbove`): `#2`.
* `osPathS_pathIn`: a spine's path is such a path.
-/
module

public import LinuxFs.Proof.os.SharedAu

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- `p` is strictly below a root of `R` (`OsState.TreeName` of a state with roots `R`). -/
def RootsTreeName (R : Roots) (p : GoString) : Prop := ∃ rj ∈ R, CanonBelow rj.1 p

/-- `p` is a root of `R` followed by valid components. -/
def PathIn (R : Roots) (p : GoString) : Prop :=
  ∃ r j0 cs, (r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs

/-- A path of the roots is a `TreeName` or a root. -/
theorem pathIn_kind {st : OsState} {p : GoString} (h : PathIn st.fs.roots p) :
    st.TreeName p ∨ ∃ rj ∈ st.fs.roots, rj.1 = p := by
  obtain ⟨r, j0, cs, hm, hcs, rfl⟩ := h
  rcases cs with _ | ⟨c, cs⟩
  · right; exact ⟨(r, j0), hm, by simp [joinPath]⟩
  · left; exact ⟨(r, j0), hm, c :: cs, by simp, hcs, rfl⟩

theorem pathIn_treePath {st : OsState} {p : GoString} (h : PathIn st.fs.roots p) : st.TreePath p := by
  rcases pathIn_kind h with h | h
  · exact .inr h
  · exact .inl h

theorem pathIn_child {R : Roots} {d b : GoString} (h : PathIn R d) (hb : NameOk b) :
    PathIn R (child d b) := by
  obtain ⟨r, j0, cs, hm, hcs, rfl⟩ := h
  refine ⟨r, j0, cs ++ [b], hm, fun c hc => ?_, (joinPath_snoc r cs b).symm⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact hcs c hc
  · simp at hc; subst hc; exact hb

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- A spine's path is a path of the roots; the spine kept. -/
theorem osPathS_pathIn_keep (R : Roots) (p : GoString) (dq : DFrac) (j : Ino) :
    osPathS (L := L) R p dq j ⊢ ⌜RootsOk R ∧ PathIn R p⌝ ∗ osPathS (L := L) R p dq j := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %hp, Hs⟩
  isplitr
  · ipureintro
    obtain ⟨hR, hm, hcs, rfl⟩ := hp
    exact ⟨hR, r, j0, cs, hm, hcs, rfl⟩
  iexists r, j0, cs
  iframe Hs
  ipureintro; exact hp

/-- A spine's path is a path of the roots. -/
theorem osPathS_pathIn (R : Roots) (p : GoString) (dq : DFrac) (j : Ino) :
    osPathS (L := L) R p dq j ⊢ ⌜RootsOk R ∧ PathIn R p⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %hp, -⟩
  ipureintro
  obtain ⟨hR, hm, hcs, rfl⟩ := hp
  exact ⟨hR, r, j0, cs, hm, hcs, rfl⟩

/-- **`PathKind(p)`** in the shared mode, for a path of the roots: `#1` strictly below a root,
`#0` otherwise; nothing changes. -/
theorem wp_osPathKindS (R : Roots) (p : GoString) (hp : PathIn R p) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗
      (∀ k : w64, ⌜(RootsTreeName R p ∧ k = 1) ∨ (¬ RootsTreeName R p ∧ k = 0)⌝ -∗ Φ (#k)) -∗
      WP (ExternalOp fsExt.name "PathKind" (Val (#p))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HΦ
  iapply wp_fs_stepM "PathKind" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases Hm with (Hm | Hm)
  · iexfalso
    unfold treeLegacy legacyHolds
    icases Hm with ⟨%V0, %Γdf, %Γc, %hns, -, -, -, -, -, Has, -⟩
    icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hl
    simp at hl
  unfold treeShared
  icases Hm with ⟨%V0, %s0, %Γdf, %Γc, %Γg, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  obtain ⟨hw, hc⟩ := hns
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hk : st.TreeName p ∨ ∃ rj ∈ st.fs.roots, rj.1 = p := by
    subst hR; exact pathIn_kind hp
  have htp : st.TreePath p := by subst hR; exact pathIn_treePath hp
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    by_cases ht : st.TreeName p
    · exact ⟨_, h, st, ⟨p, rfl, rfl, .inl ⟨ht, rfl⟩⟩, hfr, hr⟩
    · exact ⟨_, h, st, ⟨p, rfl, rfl, .inr (.inl ⟨ht, hk.resolve_left ht, rfl⟩)⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨p', hv, hst, hres⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  imod osWorld_filesSame (st := st) (st' := st) (filesSame_refl st) Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hcm]
  · try unfold treeCtx
    iframe Hcm
    iright
    try unfold treeShared
    iexists V0, s0, Γdf, Γc, Γg
    iframe
    ipureintro; exact ⟨hw, hc⟩
  have hTN : st.TreeName p ↔ RootsTreeName R p := by subst hR; rfl
  rcases hres with ⟨ht, rfl⟩ | ⟨ht, -, rfl⟩ | ⟨hnt, -, -⟩
  rotate_left 2
  · exact absurd htp hnt
  · iapply wp_value'
    iapply HΦ $$ %(1 : w64) %(.inl ⟨hTN.1 ht, rfl⟩)
  · iapply wp_value'
    iapply HΦ $$ %(0 : w64) %(.inr ⟨fun h => ht (hTN.2 h), rfl⟩)

/-- **`PathKind(p)`** in the shared mode, for a strict ancestor of a root of `R` (`RootsAbove`):
`#2`; nothing changes. -/
theorem wp_osPathKindAboveS (R : Roots) (p : GoString) (hp : RootsAbove R p) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ Φ (#(2 : w64)) -∗
      WP (ExternalOp fsExt.name "PathKind" (Val (#p))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HΦ
  iapply wp_fs_stepM "PathKind" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases Hm with (Hm | Hm)
  · iexfalso
    unfold treeLegacy legacyHolds
    icases Hm with ⟨%V0, %Γdf, %Γc, %hns, -, -, -, -, -, Has, -⟩
    icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hl
    simp at hl
  unfold treeShared
  icases Hm with ⟨%V0, %s0, %Γdf, %Γc, %Γg, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  obtain ⟨hw, hc⟩ := hns
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hntp : ¬ st.TreePath p := by subst hR; exact rootsAbove_not_treePath hcoh.1 hp
  have hab : st.AboveRoot p := by subst hR; exact hp
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨p, rfl, rfl, .inr (.inr ⟨hntp, hab, rfl⟩)⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨p', hv, hst, hres⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  imod osWorld_filesSame (st := st) (st' := st) (filesSame_refl st) Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hcm]
  · try unfold treeCtx
    iframe Hcm
    iright
    try unfold treeShared
    iexists V0, s0, Γdf, Γc, Γg
    iframe
    ipureintro; exact ⟨hw, hc⟩
  rcases hres with ⟨ht, -⟩ | ⟨-, hr0, -⟩ | ⟨-, -, rfl⟩
  · exact absurd (.inr ht) hntp
  · exact absurd (.inl hr0) hntp
  iapply wp_value'
  iexact HΦ


end specs

end Fs
end Perennial

end
