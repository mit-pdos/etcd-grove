/-
Iris reasoning principles for the issue-record extension (`Impl.lean`; the restart plan's R2c stage
2, 2026-11-02): the durable-state extension's (`GooseLang/Ext/Durable/Specs.lean`) for a map from ids
to generators.

* The ghost state: one ghost variable holding the record (`idIssueOwn M`), half in the state
  interpretation and half the program's; a program puts its half in an invariant (the cluster's
  claims, `idClusterInv`) and uses the atomic spec.
* `wp_IdIssue_atomic`: `"Issue"` of `(id, g)` returns `idIssueOk M id g` and leaves `idIssueNext M
  id g`.
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

/-- What the adequacy theorem provides: ghost variables. -/
class IdIssueGpreS (GF : BundledGFunctors) where
  idIssuePreAllG : AllG GF

/-- The ghost variable of the record. -/
structure IdIssueGS (GF : BundledGFunctors) where
  idIssueAllG : AllG GF
  idIssueName : GName

section durable
variable {GF : BundledGFunctors}

/-- The record is `fs`, with fraction `q` (a half is the program's, a half the state
interpretation's). -/
def idIssueVar (hL : IdIssueGS GF) (q : Qp) (fs : IdIssueState) : IProp GF :=
  letI := hL.idIssueAllG
  ghostVar hL.idIssueName q fs

/-- The interpretation of the record. -/
def idIssueCtx (hL : IdIssueGS GF) (fs : IdIssueState) : IProp GF :=
  idIssueVar hL (1 : Qp).half fs

instance idIssueVar_timeless (hL : IdIssueGS GF) (q : Qp) (fs : IdIssueState) :
    Timeless (idIssueVar hL q fs) := by
  unfold idIssueVar; infer_instance

theorem idIssue_local_init (hPre : IdIssueGpreS GF) (fs : IdIssueState) :
    ⊢@{IProp GF} |==> ∃ hL : IdIssueGS GF, idIssueCtx hL fs ∗ idIssueVar hL (1 : Qp).half fs := by
  letI := hPre.idIssuePreAllG
  imod ghostVar_alloc (GF := GF) fs with ⟨%γ, H⟩
  imodintro
  iexists (⟨hPre.idIssuePreAllG, γ⟩ : IdIssueGS GF)
  unfold idIssueCtx idIssueVar
  iapply (ghostVar_split_half γ 1 fs).mp
  iexact H

end durable

/-- The ghost state of the issue record. The program gets its half of the initial record. -/
instance idIssue_interp : ExtInterp idIssueExt where
  LocalGS := IdIssueGS
  GlobalGS _ := Unit
  localCtx := idIssueCtx
  globalCtx _ _ := iprop(True)
  PreG := IdIssueGpreS
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart hL fs := idIssueVar hL (1 : Qp).half fs
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre fs _ _ := idIssue_local_init hPre fs

/-! ## Specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [GoGlobalContext]
  
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev gooseIdIssueGS : IdIssueGS GF := extLocalGS idIssueExt

/-- The record is `fs` (the program's half of the ghost variable). -/
def idIssueOwn (fs : IdIssueState) : IProp GF := idIssueVar gooseIdIssueGS (1 : Qp).half fs

instance idIssueOwn_timeless (fs : IdIssueState) : Timeless (idIssueOwn (L := L) fs) := by
  unfold idIssueOwn; infer_instance

theorem idIssue_local_ctx_eq (fs : IdIssueState) :
    ExtInterp.localCtx (E := idIssueExt) (extLocalGS idIssueExt) fs ⊣⊢
      idIssueVar (gooseIdIssueGS (L := L)) (1 : Qp).half fs := .rfl

theorem idIssueVar_agree (fs fs' : IdIssueState) :
    ⊢@{IProp GF} idIssueVar (gooseIdIssueGS (L := L)) (1 : Qp).half fs -∗
      idIssueOwn (L := L) fs' -∗ ⌜fs = fs'⌝ := by
  unfold idIssueOwn idIssueVar
  letI := (gooseIdIssueGS (L := L)).idIssueAllG
  exact ghostVar_agree _ _ _ _ _

theorem idIssueVar_update (fs fs' new : IdIssueState) :
    ⊢@{IProp GF} idIssueVar (gooseIdIssueGS (L := L)) (1 : Qp).half fs -∗
      idIssueOwn (L := L) fs' ==∗
      idIssueVar (gooseIdIssueGS (L := L)) (1 : Qp).half new ∗ idIssueOwn (L := L) new := by
  unfold idIssueOwn idIssueVar
  letI := (gooseIdIssueGS (L := L)).idIssueAllG
  exact ghostVar_update_halves _ _ _ _

/-- `"Issue"` as a logically atomic spec: the record's ownership is needed only during the step,
so it can come from an invariant. -/
theorem wp_IdIssue_atomic (id : w64) (g : Loc) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ M : IdIssueState, idIssueOwn M ∗
      (idIssueOwn (idIssueNext M id g) ={∅,E}=∗ Φ #(idIssueOk M id g)))
    ⊢ WP (ExternalOp idIssueExt.name "Issue" (Val (PairV (#id) (#g)))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep "Issue" (PairV (#id) (#g)) Φ (by simp [val.isPanic])
  iintro %h %σ %gs Hheap Hl Hg
  imod HAU with ⟨%M, Hown, Hclose⟩
  icases (idIssue_local_ctx_eq σ).mp $$ Hl with Hl
  icases idIssueVar_agree σ M $$ Hl Hown with %Heq
  subst Heq
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, _, gs, rfl, id, g, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %gs' %Hst _
  obtain ⟨rfl, id', g', Hv, rfl, rfl⟩ := Hst
  obtain ⟨Hid, Hgl⟩ := val.PairV.inj Hv
  obtain rfl := GoGlobalContext.intoVal_inj_w64 Hid
  obtain rfl := GoGlobalContext.intoVal_inj_loc Hgl
  imod idIssueVar_update σ σ (idIssueNext σ id g) $$ Hl Hown with ⟨Hl, Hown⟩
  imod Hclose $$ Hown with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (idIssue_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iexact HΦ

end lifting

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
