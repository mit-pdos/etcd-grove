/-
Iris reasoning principles for the issue-record extension (`Impl.lean`; the restart plan's R2c stage
2, 2026-11-02): the durable-state extension's (`GooseLang/Ext/Durable/Specs.lean`) for a map from ids
to generators.

* The ghost state: a ghost map of the record, its authority and every entry's persistent element in
  the state interpretation. The program owns nothing of it at the start (its start resource is
  `True`, so a `Main` takes nothing for it); it learns facts: `idIssueFrag id g`, `g` issued `id`
  (persistent; one issuer per id, `idIssueFrag_agree`).
* `wp_IdIssue`: `"Issue"` of `(id, g)` returns `b`, and with `b = true` the fact `idIssueFrag id g`
  (so `b` only if no other generator issued `id`). The mask is open around the step, for a caller
  that updates an invariant at it.
* `idIssueExts`: a program whose only extension is the record (the examples' closure).
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable
public import Perennial.Ghost.GhostVar
public import Perennial.Golang.Defn.PostLang
public import GooseLang.Ext.IdIssue.Impl

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Ghost state -/

/-- What the adequacy theorem provides: the universal camera, for a ghost map. -/
class IdIssueGpreS (GF : BundledGFunctors) where
  idIssuePreAllG : AllG GF

/-- The ghost map of the record. -/
structure IdIssueGS (GF : BundledGFunctors) where
  idIssueAllG : AllG GF
  idIssueName : GName

section ghost
variable {GF : BundledGFunctors}

/-- **`id` was issued by the generator `g`** (persistent): the record's element. -/
def idIssueFragAt (hL : IdIssueGS GF) (id : w64) (g : Loc) : IProp GF :=
  letI := hL.idIssueAllG
  id ↪[hL.idIssueName]□ g

instance idIssueFragAt_persistent (hL : IdIssueGS GF) (id : w64) (g : Loc) :
    Persistent (idIssueFragAt hL id g) := by
  unfold idIssueFragAt; infer_instance

/-- The interpretation of the record: the map's authority, and every entry's persistent element (so
that an `"Issue"` that finds its own entry hands it out again). -/
def idIssueCtx (hL : IdIssueGS GF) (M : IdIssueState) : IProp GF :=
  letI := hL.idIssueAllG
  iprop(ghostMapAuth hL.idIssueName 1 M ∗ [∗map] id ↦ g ∈ M, idIssueFragAt hL id g)

theorem idIssue_local_init (hPre : IdIssueGpreS GF) (M : IdIssueState) (hM : M = ∅) :
    ⊢@{IProp GF} |==> ∃ hL : IdIssueGS GF, idIssueCtx hL M ∗ iprop(True) := by
  letI := hPre.idIssuePreAllG
  subst hM
  imod (ghost_map_alloc_empty (GF := GF) (K := w64) (V := Loc)) with ⟨%γ, H⟩
  imodintro
  iexists (⟨hPre.idIssuePreAllG, γ⟩ : IdIssueGS GF)
  unfold idIssueCtx
  iframe H
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- **The record's step** (ghost): the record after an `"Issue"` of `(id, g)`, and, if it is
allowed, the id's element. -/
theorem idIssue_ghost_step (hL : IdIssueGS GF) (M : IdIssueState) (id : w64) (g : Loc) :
    ⊢@{IProp GF} idIssueCtx hL M ==∗
      idIssueCtx hL (idIssueNext M id g) ∗ (⌜idIssueOk M id g = true⌝ → idIssueFragAt hL id g) := by
  letI := hL.idIssueAllG
  iintro HM
  iunfold idIssueCtx at HM
  icases HM with ⟨HA, #HE⟩
  unfold idIssueNext idIssueOk
  cases hlk : M !! id with
  | none =>
    simp only [_root_.decide_true, ↓reduceIte]
    imod ghost_map_insert_persist id g hlk $$ HA with ⟨HA, #He⟩
    imodintro
    isplitl [HA]
    · iunfold idIssueCtx
      iframe HA
      iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (m := M)
        (Φ := fun i g' => idIssueFragAt hL i g') hlk).2
      iframe HE
      iunfold idIssueFragAt; iexact He
    · iintro -; iunfold idIssueFragAt; iexact He
  | some g' =>
    by_cases hg : g' = g
    · subst hg
      simp only [_root_.decide_true, ↓reduceIte, GMap.insert_id M id g' hlk]
      icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := M)
        (Φ := fun i g' => idIssueFragAt hL i g') hlk).1 $$ HE with ⟨#He, -⟩
      imodintro
      isplitl [HA]
      · iunfold idIssueCtx; iframe HA HE
      · iintro -; iexact He
    · simp only [hg, decide_false, Bool.false_eq_true, ↓reduceIte]
      imodintro
      isplitl [HA]
      · iunfold idIssueCtx; iframe HA HE
      · iintro %h; cases h

end ghost

/-- The ghost state of the issue record. The program starts with nothing: the record is empty, and
its facts come from `"Issue"`. -/
instance idIssue_interp : ExtInterp idIssueExt where
  LocalGS := IdIssueGS
  GlobalGS _ := Unit
  localCtx := idIssueCtx
  globalCtx _ _ := iprop(True)
  PreG := IdIssueGpreS
  initgP _ := True
  initP M _ := M = ∅
  globalStart _ _ := iprop(True)
  localStart _ _ := iprop(True)
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre M _ hM := idIssue_local_init hPre M hM

/-! ## Specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev gooseIdIssueGS : IdIssueGS GF := extLocalGS idIssueExt

/-- **`id` was issued by `g`** (persistent; the program's fact). -/
def idIssueFrag (id : w64) (g : Loc) : IProp GF := idIssueFragAt (gooseIdIssueGS (L := L)) id g

instance idIssueFrag_persistent (id : w64) (g : Loc) : Persistent (idIssueFrag (L := L) id g) := by
  unfold idIssueFrag; infer_instance

/-- **One issuer per id.** -/
theorem idIssueFrag_agree (id : w64) (g g' : Loc) :
    ⊢@{IProp GF} idIssueFrag (L := L) id g -∗ idIssueFrag (L := L) id g' -∗ ⌜g = g'⌝ := by
  unfold idIssueFrag idIssueFragAt
  letI := (gooseIdIssueGS (L := L)).idIssueAllG
  iintro #H1 #H2
  ihave %H := ghostMapElem_agree $$ H1 H2
  ipureintro; exact H

theorem idIssue_local_ctx_eq (M : IdIssueState) :
    ExtInterp.localCtx (E := idIssueExt) (extLocalGS idIssueExt) M ⊣⊢
      idIssueCtx (gooseIdIssueGS (L := L)) M := .rfl

/-- **`"Issue"` of `(id, g)`** (the step's spec, with its mask open for an invariant around it): its
result `b`, and with `b` the fact that `g` issued `id` -- so `b` only if no other generator has
(`idIssueFrag_agree`). -/
theorem wp_IdIssue (id : w64) (g : Loc) (Φ : val → IProp GF) :
    (|={E,∅}=> ∀ b : Bool, (⌜b = true⌝ → idIssueFrag (L := L) id g) ={∅,E}=∗ Φ #b)
    ⊢ WP (ExternalOp idIssueExt.name "Issue" (Val (PairV (#id) (#g)))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep "Issue" (PairV (#id) (#g)) Φ (by simp [val.isPanic])
  iintro %h %σ %gs Hheap Hl Hg
  imod HAU with Hclose
  icases (idIssue_local_ctx_eq σ).mp $$ Hl with Hl
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, _, gs, rfl, id, g, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %gs' %Hst _
  obtain ⟨rfl, id', g', Hv, rfl, rfl⟩ := Hst
  obtain ⟨Hid, Hgl⟩ := val.PairV.inj Hv
  obtain rfl := GoGlobalContext.intoVal_inj_w64 Hid
  obtain rfl := GoGlobalContext.intoVal_inj_loc Hgl
  imod (idIssue_ghost_step (gooseIdIssueGS (L := L)) σ id g) $$ Hl with ⟨Hl, #Hfr⟩
  ihave #Hfr' : iprop(⌜idIssueOk σ id g = true⌝ → idIssueFrag (L := L) id g) $$ []
  · iunfold idIssueFrag; iexact Hfr
  imod Hclose $$ %(idIssueOk σ id g) Hfr' with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (idIssue_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iexact HΦ

end lifting

/-! ## The fact without the extension's instance

`idutil`'s definitions (the cluster's claims, the generators) are stated over every program, not only
those whose extensions include the record (`HasExt idIssueExt` is a `Prop`, and the server's own
definitions do not take it). They read the record's fact through `idIssueFragD`, which is
`idIssueFrag` when the program has the extension and `False` otherwise; only the proofs that step
through `"Issue"` (`Generator.Next`'s) take the instance, and rewrite with `idIssueFragD_eq`. -/

section instanceFree
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [L : GooseLocalGS GF]

open Classical in
/-- **`id` was issued by `g`, read without the instance** (see above). -/
noncomputable def idIssueFragD (id : w64) (g : Loc) : IProp GF :=
  if h : HasExt idIssueExt then (haveI := h; idIssueFrag (L := L) id g) else iprop(False)

instance idIssueFragD_persistent (id : w64) (g : Loc) : Persistent (idIssueFragD (L := L) id g) := by
  unfold idIssueFragD; split <;> infer_instance

instance idIssueFragD_timeless (id : w64) (g : Loc) : Timeless (idIssueFragD (L := L) id g) := by
  unfold idIssueFragD; split
  · unfold idIssueFrag idIssueFragAt; infer_instance
  · infer_instance

/-- Under the instance, the fact itself. -/
theorem idIssueFragD_eq [h : HasExt idIssueExt] (id : w64) (g : Loc) :
    idIssueFragD (L := L) id g = idIssueFrag (L := L) id g := by
  unfold idIssueFragD; rw [dif_pos h]

/-- One issuer per id (`idIssueFrag_agree`'s). -/
theorem idIssueFragD_agree (id : w64) (g g' : Loc) :
    ⊢@{IProp GF} idIssueFragD (L := L) id g -∗ idIssueFragD (L := L) id g' -∗ ⌜g = g'⌝ := by
  by_cases h : HasExt idIssueExt
  · haveI := h
    rw [idIssueFragD_eq, idIssueFragD_eq]
    exact idIssueFrag_agree id g g'
  · unfold idIssueFragD; rw [dif_neg h]
    iintro H; iexfalso; iexact H

end instanceFree

/-! ## A closed program -/

section closed

/-- A program whose only extension is the issue record. -/
@[reducible] def idIssueExts : GooseExts := ⟨[idIssueExt]⟩

attribute [local instance] idIssueExts

@[reducible] def idIssueExtsSemantics : GooseSemantics := ⟨(idIssue_semantics, ⟨⟩)⟩

@[reducible] def idIssueExtsInterp : GooseInterp := ⟨(idIssue_interp, ⟨⟩)⟩

attribute [local instance] idIssueExtsSemantics idIssueExtsInterp

/-- Closing off a program proves `HasExt` by computation. Not an instance (it holds only under
`idIssueExts`): a closed theorem makes it a local one. -/
theorem idIssueExts_hasExt : HasExt idIssueExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

end closed

end Perennial
