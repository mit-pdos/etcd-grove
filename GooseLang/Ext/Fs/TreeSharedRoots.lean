/-
**Two shared invariants are of one set of roots** (S5, 2026-11-18, `notes/bbolt-integration-plan.md`):
the shared mode's invariant `osSharedInv R` holds the whole element `(R, Vs)` of the ghost map `γs`,
whose authority is in the state interpretation (`treeShared`: at the state's roots; `treeLegacy`:
empty). At the step of any expression that is not a value (`wp_ext_acc`), each of two invariants,
opened in turn, finds its roots the state's, so the two agree (`wp_osSharedAgree`). What lets a
client combine two claims made with different witnesses of the roots (a file's and a target name's,
for a rename, `Proof/os/Rename.lean`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedSwitch

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **A shared invariant's roots are the state's** (and the tree is in the shared mode). -/
theorem treeCtx_roots (R : Roots) (st : OsState) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ treeCtx (gooseOsGS (L := L)) st ={E}=∗
      ⌜R = st.fs.roots⌝ ∗ treeCtx (gooseOsGS (L := L)) st := by
  iintro #Hsi Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  unfold osSharedInv
  icases Hm with (Hm | Hm)
  · unfold treeLegacy legacyHolds
    icases Hm with ⟨%V, %Γdf, %Γc, %hns, HAd, HAdf, HAc, Hrd, Hcr, Has, -⟩
    imod inv_acc hE $$ Hsi with ⟨Hi, -⟩
    icases Hi with >Hi
    icases Hi with ⟨%Vs, %Γn, Hs, -⟩
    icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %h
    exact absurd h (by simp)
  · unfold treeShared
    icases Hm with ⟨%V0, %s1, %Γdf, %Γc, %Γg, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr, HAg,
      Hgr⟩
    imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
    icases Hi with >Hi
    icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
    icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
    simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
    obtain ⟨hR, rfl⟩ := hVs
    imod Hclose $$ [Hs HAn Halen HAlog] with -
    · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
    imodintro
    isplitr
    · ipureintro; exact hR.symm
    iframe Hcm
    iright
    iexists V0, s1, Γdf, Γc, Γg
    iframe
    ipureintro; exact hns

/-- **Two shared invariants agree on the roots**, at the step of any expression that is not a
value (see the file header). -/
theorem wp_osSharedAgree (R R' : Roots) (e : Expr) (he : toVal e = none) (hE : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osSharedInv (L := L) R -∗ osSharedInv (L := L) R' -∗
      (⌜R = R'⌝ -∗ WP e @ s; E {{ Φ }}) -∗ WP e @ s; E {{ Φ }} := by
  iintro #Hsi #Hsi' HΦ
  iapply wp_ext_acc (X := fsExt) e Φ he
  iintro %σ %g Hl Hg
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx
  icases Hl with ⟨HF, Ht, Hof⟩
  imod treeCtx_roots R σ hE $$ Hsi Ht with ⟨%h1, Ht⟩
  imod treeCtx_roots R' σ hE $$ Hsi' Ht with ⟨%h2, Ht⟩
  imodintro
  isplitl [HF Ht Hof]
  · iapply (os_local_ctx_eq σ).mpr
    unfold osCtx
    iframe
  iframe Hg
  iapply HΦ
  ipureintro; exact h1.trans h2.symm

end specs

end Fs
end Perennial
