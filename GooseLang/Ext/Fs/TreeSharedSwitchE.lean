/-
**The mode switch at any step** (S3e, 2026-11-17): `wp_osShare'` (`TreeSharedSwitch.lean`) at the
step of any expression that is not a value, not only an operation of the extension. The switch reads
and rewrites only the extension's part of the state interpretation, which every step of the program
gives access to (`wp_ext_acc`), so it may be done before the program's first step: a closed theorem
that starts in the legacy mode (`fs_start`'s whole tree) switches at once, before handing the proof
of its program the shared mode's claims (`Proof/runtime/StartFiles.lean`). Untrusted.
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

/-- **The mode switch, at the step of any expression that is not a value**: `wp_osShare'`. -/
theorem wp_osShareE (R : Roots) (V : Hist) (e : Expr) (he : toVal e = none) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own 1) R V -∗
      (osSharedInv (L := L) R -∗ osCallPerm (L := L) 1 -∗ osLogLb (L := L) V.2.length -∗
        ([∗list] j ∈ (GMap.toList V.now).map (·.1),
          osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) -∗
        WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  iintro #Hinv Hh HΦ
  iapply wp_ext_acc (X := fsExt) e Φ he
  iintro %σ %g Hl Hg
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx
  icases Hl with ⟨HF, Ht, Hof⟩
  icases treeCtx_legacy _ (legacyWit_tree _ _ _) σ $$ Hh Ht with ⟨Hh, Ht, Hcm⟩
  unfold treeLegacy legacyHolds
  icases Ht with ⟨%V0, %Γdf, %Γc, %hns, HAd, HAdf, HAc, Hrd, Hcr, Has, Hadfs, Hacs, Hperm, Han,
    Halen, Halog, Hag⟩
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  icases whole_alone _ _ Γdf Γc $$ Hh Hrd Hcr with ⟨%Hal, Hh, -, -⟩
  obtain ⟨hdf, hcl⟩ := Hal
  have hcohS := cohS_switch hns.2 hdf hcl
  have hV : V = (σ.fs.treeDur, σ.fs.metaLog) := hns.2.hist
  subst hdf hcl
  imod gAuth_insert _ _ _ () (σ.fs.roots, V) (by rfl) $$ Has with ⟨Has, Hs⟩
  rw [histMap_insert_empty]
  imod (letI := (gooseOsGS (L := L)).osAllG;
    mono_nat_own_update (γ := (gooseOsGS (L := L)).γlen) V.2.length (Nat.zero_le _)) $$ Halen
    with ⟨Halen, #Hlb⟩
  imod log_alloc _ V.2 $$ Halog with Halog
  imod claims_alloc _ V _ (GMap.toList_keys_nodup _) $$ Han with ⟨Han, Hcl⟩
  imod inv_alloc osShN E iprop(∃ (Vs : Hist) (Γn : GMap (Ino × NameSet) NamesH),
    gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs () (DFrac.own 1) (σ.fs.roots, Vs) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ ⌜RootsOk σ.fs.roots ∧ NamesCoh Vs Γn⌝ ∗
    (letI := (gooseOsGS (L := L)).osAllG; monoNatAuthOwn (gooseOsGS (L := L)).γlen 1 Vs.2.length) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog (logMap Vs.2)) $$ [Hs Han Halen Halog]
    with #Hsi
  · inext
    iexists V, (claimsInit V ((GMap.toList V.now).map (·.1)))
    iframe Hs Han Halen Halog
    ipureintro; exact ⟨hns.1.roots, namesCoh_init V (by rw [hV]; exact hcohS.starts)⟩
  imodintro
  isplitl [HF Hh HAd HAdf HAc Has Hadfs Hacs Hag Hcm Hof]
  · iapply (os_local_ctx_eq σ).mpr
    unfold osCtx treeCtx
    iframe HF Hcm Hof
    iright
    unfold treeShared
    iexists V, σ.fs.metaLog.length, ∅, ∅, ∅
    rw [← hV]
    unfold osTree
    iframe HAd Hh HAdf HAc Has Hadfs Hacs Hag
    isplitr
    · ipureintro; exact ⟨hns.1, hcohS⟩
    unfold callResS
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepM.bigSepM_empty.2; itrivial
  iframe Hg
  simp only [osNames_except]
  unfold osSharedInv osCallPerm osLogLb
  iapply HΦ $$ Hsi Hperm Hlb Hcl

end specs

end Fs
end Perennial
