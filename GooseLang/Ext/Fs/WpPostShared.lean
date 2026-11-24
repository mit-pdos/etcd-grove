/-
`wp_ext_postS` (`WpPost.lean`) for the file-system extension in the shared mode (wal-safe,
2026-11-22, step 2 (D), design (FNE) of `notes/wal-units/tester.md`): the fact `QP` the step finds of
the state is read through the claims' authority (`osSharedInv`, opened for an instant at the step),
from the caller's resources `F`, as `wp_callEndS`'s `hF` reads it. So a spec of a call proved over
any semantics gives, over a semantics whose premise (`NoIoErr`) restricts the call's outcomes in the
states `QP` holds of, the restricted outcomes (`hΨ`), without re-proving the step. Untrusted.
-/
module

public import GooseLang.Ext.Fs.WpPost
public import GooseLang.Ext.Fs.TreeSharedStep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The tree's interpretation, with the shared invariant, gives the fact
`QP` the caller's resources `F` give through the claims' authority (`hF`), and the state's
well-formedness and roots. -/
theorem treeCtx_readS (R : Roots) (F : IProp GF) (QP : OsState → Prop)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜QP st⌝)
    (st : OsState) (hE' : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ F -∗ treeCtx (gooseOsGS (L := L)) st -∗
      |={E}=> ⌜QP st ∧ FsTreeWf st ∧ st.fs.roots = R⌝ ∗ F ∗ treeCtx (gooseOsGS (L := L)) st := by
  iintro #Hsi HF Ht
  unfold osSharedInv
  imod inv_acc hE' $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases (treeCtx_eq _ _).1 $$ Ht with ⟨Ht, Hcm⟩
  unfold treeCtxT
  icases Ht with ⟨%Γdf, %Γc, %Γg, %hns, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  icases hF st Γn hR hcoh.2 $$ HAn HF with %hP
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  imodintro
  isplitr
  · ipureintro; exact ⟨hP, hns.1, hR⟩
  iframe HF
  iapply (treeCtx_eq _ _).2
  iframe Hcm
  unfold treeCtxT
  iexists Γdf, Γc, Γg
  try unfold callResS
  iframe
  ipureintro; exact hns

/-- **A weakest precondition of a file-system call in the shared mode, strengthened by its steps
from the states the caller's resources `F` read** (see the file header). -/
theorem wp_fs_postSh (o : String) (v : val) (hv : v.isPanic = false) (R : Roots) (F : IProp GF)
    (QP : OsState → Prop)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜QP st⌝)
    (Ψ : val → Prop)
    (hΨ : ∀ h st g e' h' st' g', QP st → FsTreeWf st → st.fs.roots = R →
      ExtSemantics.step (E := fsExt) o v h st g e' h' st' g' → ∃ r, e' = Val r ∧ Ψ r)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osSharedInv (L := L) R -∗ F -∗
      (F -∗ WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ r, ⌜Ψ r⌝ -∗ Φ r }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) (ExternalOp fsExt.name o (Val v)) = none := rfl
  iintro #Hsi HP Hwp
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, c⟩
  icases (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  icases (goose_stateInterp_eq σ ns (obs ++ obs') nt).1 $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
  icases HasExt.localCtx_acc (X := fsExt) _ $$ Hext with ⟨Hl, Hlclose⟩
  icases (os_local_ctx_eq _).mp $$ Hl with Hl
  unfold osCtx
  icases Hl with ⟨Hf, Htr, Hof, Hlk⟩
  imod treeCtx_readS R F QP hF _ hE' $$ Hsi HP Htr with ⟨%hR, HP, Htr⟩
  ihave Hl := (os_local_ctx_eq _).mpr $$ [Hf Htr Hof Hlk]
  · unfold osCtx; iframe
  ihave Hσ : stateInterp (GF := GF) ((σ, c) : BcfgState) ns (obs ++ obs') nt $$
    [Hheap Hl Hlclose Hgs Hgext Hproph Hc Ht Hnc]
  · iapply (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).2
    iframe Hc Ht Hnc
    iapply (goose_stateInterp_eq σ ns (obs ++ obs') nt).2
    ihave Hl := Hlclose $$ Hl
    rw [ExtIn.set_get]
    iframe
    ipureintro; exact Hlctx
  ihave Hwp := Hwp $$ HP
  ihave Hwp := wp_unfold.1 $$ Hwp
  unfold wp.pre
  rw [h']
  dsimp only
  imod Hwp $$ %(σ, c) %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨h, g, h', σ', g', Hst⟩ := extOp_step_inv (X := fsExt) o v hv Hstep
  obtain ⟨r, rfl, hr⟩ := hΨ _ _ _ _ _ _ _ hR.1 hR.2.1 hR.2.2 Hst
  ihave H := H $$ %(Val r) %σ₂ %eₜ %Hstep Hcred
  iapply step_fupdN_wand $$ H
  iintro H
  imod H with ⟨Hσ, Hwp, Hefs⟩
  imodintro
  iframe Hσ Hefs
  iapply wp_value_fupd'.2
  imod wp_value_fupd'.1 $$ Hwp with Hwp
  imodintro
  iapply Hwp
  ipureintro; exact hr

end specs

end Fs
end Perennial

end
