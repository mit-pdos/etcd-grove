/-
Iris reasoning principles for the durable-state extension.

Notes:
* The ghost state is one ghost variable holding all the files (`durableOwn fs`, `fs` the map
  from names to contents), half of it in the state interpretation and half the program's:
  unlike points-to facts per file, it says which files do not exist, which a read returns.
  A program that shares the files puts `durableOwn` in an invariant (the atomic specs). It is
  per generation (`LocalGS`); there is no crash reasoning yet (no crash adequacy instance, as
  Perennial's `fsExt` has).
* The specs hold for any program whose extensions include the durable state
  (`HasExt durableExt`), with an injective encoding of strings as values.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.Ghost.GhostVar
public import Perennial.Golang.Defn.PostLang
public import GooseLang.Ext.Durable.Impl

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Ghost state -/

/-- What the adequacy theorem provides: ghost variables. -/
class DurableGpreS (GF : BundledGFunctors) where
  durablePreAllG : AllG GF

/-- The ghost variable of the files. -/
structure DurableGS (GF : BundledGFunctors) where
  durableAllG : AllG GF
  durableName : GName

section durable
variable {GF : BundledGFunctors}

/-- The files are `fs`, with fraction `q` (a half is the program's, a half the state
interpretation's). -/
def durableVar (hL : DurableGS GF) (q : Qp) (fs : DurableState) : IProp GF :=
  letI := hL.durableAllG
  ghostVar hL.durableName q fs

/-- The interpretation of the files. -/
def durableCtx (hL : DurableGS GF) (fs : DurableState) : IProp GF :=
  durableVar hL (1 : Qp).half fs

instance durableVar_timeless (hL : DurableGS GF) (q : Qp) (fs : DurableState) :
    Timeless (durableVar hL q fs) := by
  unfold durableVar; infer_instance

theorem durable_local_init (hPre : DurableGpreS GF) (fs : DurableState) :
    ⊢@{IProp GF} |==> ∃ hL : DurableGS GF, durableCtx hL fs ∗ durableVar hL (1 : Qp).half fs := by
  letI := hPre.durablePreAllG
  imod ghostVar_alloc (GF := GF) fs with ⟨%γ, H⟩
  imodintro
  iexists (⟨hPre.durablePreAllG, γ⟩ : DurableGS GF)
  unfold durableCtx durableVar
  iapply (ghostVar_split_half γ 1 fs).mp
  iexact H

end durable

/-- The ghost state of the durable state. The program gets its half of the initial files. -/
instance durable_interp : ExtInterp durableExt where
  LocalGS := DurableGS
  GlobalGS _ := Unit
  localCtx := durableCtx
  globalCtx _ _ := iprop(True)
  PreG := DurableGpreS
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart hL fs := durableVar hL (1 : Qp).half fs
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre fs _ _ := durable_local_init hPre fs

/-! ## Specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt] [GoGlobalContext]
  [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev gooseDurableGS : DurableGS GF := extLocalGS durableExt

/-- The node's files are `fs` (the program's half of the ghost variable). -/
def durableOwn (fs : DurableState) : IProp GF := durableVar gooseDurableGS (1 : Qp).half fs

instance durableOwn_timeless (fs : DurableState) : Timeless (durableOwn (L := L) fs) := by
  unfold durableOwn; infer_instance

theorem durable_local_ctx_eq (fs : DurableState) :
    ExtInterp.localCtx (E := durableExt) (extLocalGS durableExt) fs ⊣⊢
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs := .rfl

theorem durableVar_agree (fs fs' : DurableState) :
    ⊢@{IProp GF} durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs -∗
      durableOwn (L := L) fs' -∗ ⌜fs = fs'⌝ := by
  unfold durableOwn durableVar
  letI := (gooseDurableGS (L := L)).durableAllG
  exact ghostVar_agree _ _ _ _ _

theorem durableVar_update (fs fs' new : DurableState) :
    ⊢@{IProp GF} durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs -∗
      durableOwn (L := L) fs' ==∗
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half new ∗ durableOwn (L := L) new := by
  unfold durableOwn durableVar
  letI := (gooseDurableGS (L := L)).durableAllG
  exact ghostVar_update_halves _ _ _ _

/-- `Read` as a logically atomic spec: the files' ownership is needed only during the step,
so it can come from an invariant. -/
theorem wp_DurableRead_atomic (f : GoString) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ fs : DurableState, durableOwn fs ∗
      (durableOwn fs ={∅,E}=∗ Φ (durableReadResult fs f)))
    ⊢ WP (ExternalOp (extOp durableExt DurableOp.ReadOp) (Val (#f))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep DurableOp.ReadOp (#f) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  imod HAU with ⟨%fs, Hown, Hclose⟩
  icases (durable_local_ctx_eq σ).mp $$ Hl with Hl
  icases durableVar_agree σ fs $$ Hl Hown with %Heq
  subst Heq
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, σ, g, rfl, f, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, f', Hv, rfl, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj Hv
  imod Hclose $$ Hown with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (durable_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iexact HΦ

/-- `Write` as a logically atomic spec. -/
theorem wp_DurableWrite_atomic (f data : GoString) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ fs : DurableState, durableOwn fs ∗
      (durableOwn (<[f := data]> fs) ={∅,E}=∗ Φ #()))
    ⊢ WP (ExternalOp (extOp durableExt DurableOp.WriteOp) (Val (PairV (#f) (#data)))) @ s; E
      {{ Φ }} := by
  iintro HAU
  iapply wp_extStep DurableOp.WriteOp (PairV (#f) (#data)) Φ (by simp [val.isPanic])
  iintro %h %σ %g Hheap Hl Hg
  imod HAU with ⟨%fs, Hown, Hclose⟩
  icases (durable_local_ctx_eq σ).mp $$ Hl with Hl
  icases durableVar_agree σ fs $$ Hl Hown with %Heq
  subst Heq
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, _, g, rfl, f, data, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, f', data', Hv, rfl, rfl⟩ := Hst
  obtain ⟨Hf, Hdata⟩ := val.PairV.inj Hv
  obtain rfl := go.intoVal_inj Hf
  obtain rfl := go.intoVal_inj Hdata
  imod durableVar_update σ σ (<[f := data]> σ) $$ Hl Hown with ⟨Hl, Hown⟩
  imod Hclose $$ Hown with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (durable_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iexact HΦ

theorem wp_DurableRead (f : GoString) (fs : DurableState) :
    {{ (durableOwn fs : IProp GF) }} (ExternalOp (extOp durableExt DurableOp.ReadOp) (Val (#f)))
      @ s; E
    {{ RET (durableReadResult fs f); durableOwn fs }} := by
  iintro %Φ Hown HΦ
  iapply wp_extStep DurableOp.ReadOp (#f) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (durable_local_ctx_eq σ).mp $$ Hl with Hl
  icases durableVar_agree σ fs $$ Hl Hown with %Heq
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, σ, g, rfl, f, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, f', Hv, rfl, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj Hv
  imod Hclose
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (durable_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iapply HΦ
  iexact Hown

theorem wp_DurableWrite (f data : GoString) (fs : DurableState) :
    {{ (durableOwn fs : IProp GF) }}
      (ExternalOp (extOp durableExt DurableOp.WriteOp) (Val (PairV (#f) (#data)))) @ s; E
    {{ RET #(); durableOwn (<[f := data]> fs) }} := by
  iintro %Φ Hown HΦ
  iapply wp_extStep DurableOp.WriteOp (PairV (#f) (#data)) Φ (by simp [val.isPanic])
  iintro %h %σ %g Hheap Hl Hg
  icases (durable_local_ctx_eq σ).mp $$ Hl with Hl
  icases durableVar_agree σ fs $$ Hl Hown with %Heq
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, _, g, rfl, f, data, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, f', data', Hv, rfl, rfl⟩ := Hst
  obtain ⟨Hf, Hdata⟩ := val.PairV.inj Hv
  obtain rfl := go.intoVal_inj Hf
  obtain rfl := go.intoVal_inj Hdata
  imod durableVar_update σ σ (<[f := data]> σ) $$ Hl Hown with ⟨Hl, Hown⟩
  imod Hclose
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (durable_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iapply HΦ
  iexact Hown

end lifting

/-! ## A closed program -/

section closed

/-- A program whose only extension is the durable state. -/
@[reducible] def durableExts : GooseExts := ⟨[durableExt]⟩

attribute [local instance] durableExts

@[reducible] def durableExtsSemantics : GooseSemantics := ⟨(durable_semantics, ⟨⟩)⟩

@[reducible] def durableExtsInterp : GooseInterp := ⟨(durable_interp, ⟨⟩)⟩

attribute [local instance] durableExtsSemantics durableExtsInterp

/-- Closing off a program proves `HasExt` by computation: `durableExt` is the program's
extension named `durableExt.name`, with its semantics and ghost state. -/
example : HasExt durableExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

end closed

end Perennial
