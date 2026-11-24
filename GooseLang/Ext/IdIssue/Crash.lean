/-
The issue record's crash interpretation (etcd-dist D4b, 2026-11-24; `Impl.lean`'s crash: every entry
kept, as an earlier incarnation's, `idIssueCrash`). Untrusted.

**A crash** gives the restarted incarnation a new ghost map of the record (`hL'`), holding every entry
the old ghost map had, each as an earlier incarnation's (`id ↦ none`, persisted), so that a generator
of the new incarnation can be proved to issue none of them (`idIssueFrag_past`). The crash's rest
(`idIssueCrashStart hL hL'`, the `crashStart` the restarted boot program gets) keeps the old map's
authority: with it, every fact of the old incarnation about an id (`idIssueElemAt hL id v`: issued by
its generator `g`, `v = some g`, or by an earlier one, `none`) becomes the new incarnation's
`idIssuePastAt hL' id` (`idIssueCrashStart_past`). So an invariant that kept the old incarnation's
facts of the ids it issued (`idPfxBody`'s `idIssueFragD id g`) can be carried across the crash as
facts that those ids are the past's.
-/
module

public import Perennial.GooseLang.CrashAdequacy
public import GooseLang.Ext.IdIssue.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section ghost
variable {GF : BundledGFunctors}

/-- **The crash's rest** (from the incarnation `hL` to the restarted one `hL'`): the old ghost map's
authority `Mg`, and every entry of `Mg` in the new map, as an earlier incarnation's. -/
def idIssueCrashStart (hL hL' : IdIssueGS GF) : IProp GF :=
  letI := hL.idIssueAllG
  iprop(∃ Mg : IdIssueState, ghostMapAuth hL.idIssueName 1 Mg ∗
    [∗map] id ↦ v ∈ idIssueCrash Mg, idIssueElemAt hL' id v)

/-- **An old incarnation's fact about `id`, after the crash**: `id` was issued by an earlier
incarnation (of `hL'`'s). -/
theorem idIssueCrashStart_past (hL hL' : IdIssueGS GF) (id : w64) (v : Option Loc) :
    ⊢@{IProp GF} idIssueCrashStart hL hL' -∗ idIssueElemAt hL id v -∗
      idIssueCrashStart hL hL' ∗ idIssuePastAt hL' id := by
  iintro Hc #He
  iunfold idIssueCrashStart at Hc
  icases Hc with ⟨%Mg, HA, #HE⟩
  letI := hL.idIssueAllG
  iunfold idIssueElemAt at He
  ihave %Hl := ghost_map_lookup $$ HA He
  have hc : idIssueCrash Mg !! id = some none := by
    have h1 : Mg !! id = some v := Hl
    show (Mg !! id).map (fun _ => (none : Option Loc)) = some none
    rw [h1]; rfl
  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := idIssueCrash Mg)
    (Φ := fun i v => idIssueElemAt hL' i v) hc).1 $$ HE with ⟨#Hp, -⟩
  isplitl [HA]
  · iunfold idIssueCrashStart
    iexists Mg
    iframe HA HE
  · iunfold idIssuePastAt; iexact Hp

/-- The ghost state's crash: a new ghost map, every old entry an earlier incarnation's. -/
theorem idIssue_local_crash (hL : IdIssueGS GF) (M : IdIssueState) :
    ⊢@{IProp GF} idIssueCtx hL M ==∗
      ∃ hL' : IdIssueGS GF, idIssueCtx hL' (idIssueCrash M) ∗ idIssueCrashStart hL hL' := by
  letI := hL.idIssueAllG
  iintro HM
  iunfold idIssueCtx at HM
  icases HM with ⟨%Mg, HA, -, %Hsub⟩
  imod (ghost_map_alloc (GF := GF) (idIssueCrash Mg)) with ⟨%γ, HA', Hs⟩
  ihave Hs2 : iprop(|==> [∗map] k ↦ v ∈ idIssueCrash Mg, k ↪[γ]□ v) $$ [Hs]
  · iapply BigSepM.bigSepM_bupd
    iapply BigSepM.bigSepM_impl $$ Hs
    iintro !> %k %v %Heq H
    iapply ghostMapElem_persist $$ H
  imod Hs2 with #Hs
  imodintro
  iexists (⟨hL.idIssueAllG, γ⟩ : IdIssueGS GF)
  isplitl [HA']
  · iunfold idIssueCtx
    iexists (idIssueCrash Mg)
    iframe HA'
    isplitl
    · iunfold idIssueElemAt; iexact Hs
    · ipureintro
      intro id v h
      have h' : (Mg !! id).map (fun _ => (none : Option Loc)) = some v := h
      show (M !! id).map (fun _ => (none : Option Loc)) = some v
      cases hm : Mg !! id with
      | none => rw [hm] at h'; cases h'
      | some w => rw [hm] at h'; cases h'; rw [Hsub id w hm]; rfl
  · iunfold idIssueCrashStart
    iexists Mg
    iframe HA
    iunfold idIssueElemAt; iexact Hs

end ghost

/-- **The issue record's crash interpretation**: a new ghost map with every old entry an earlier
incarnation's (`idIssue_local_crash`), and the crash's rest `idIssueCrashStart`. -/
instance idIssue_crash_interp : ExtCrashInterp idIssueExt where
  crashStart hL hL' := idIssueCrashStart hL hL'
  local_crash _ _ hL σ σ' h := by
    obtain rfl := (show σ' = idIssueCrash σ from h)
    exact idIssue_local_crash hL σ

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The old incarnation's fact `idIssueFrag id g`, after the crash** (the program's terms: `L` the
old incarnation's local ghost state, `L'` the restarted one's): `id` is the past's. -/
theorem idIssueFrag_crash_past (L L' : GooseLocalGS GF) (id : w64) (g : Loc) :
    ⊢@{IProp GF} idIssueCrashStart (gooseIdIssueGS (L := L)) (gooseIdIssueGS (L := L')) -∗
      idIssueFrag (L := L) id g -∗
      idIssueCrashStart (gooseIdIssueGS (L := L)) (gooseIdIssueGS (L := L')) ∗
        idIssuePast (L := L') id :=
  idIssueCrashStart_past _ _ id (some g)

/-- **The old incarnation's fact `idIssuePast id`, after the crash**: still the past's. -/
theorem idIssuePast_crash_past (L L' : GooseLocalGS GF) (id : w64) :
    ⊢@{IProp GF} idIssueCrashStart (gooseIdIssueGS (L := L)) (gooseIdIssueGS (L := L')) -∗
      idIssuePast (L := L) id -∗
      idIssueCrashStart (gooseIdIssueGS (L := L)) (gooseIdIssueGS (L := L')) ∗
        idIssuePast (L := L') id :=
  idIssueCrashStart_past _ _ id none

end lifting

end Perennial
