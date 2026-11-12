/-
Iris reasoning principles for the durable-state extension.

Notes:
* The ghost state is one ghost variable holding all the files (`durableOwn fs`, `fs` the map
  from names to contents), half of it in the state interpretation and half the program's:
  unlike points-to facts per file, it says which files do not exist, which a read returns.
  A program that shares the files puts `durableOwn` in an invariant (the atomic specs). Its crash
  interpretation (`Crash.lean`) keeps the ghost names.
* The WAL area's reservation (WAL W4a revision, 2026-11-11): a second ghost name holds a ghost map
  at the one key `()`, empty while no area is reserved. `durableOwn fs` holds its authority, which
  `durable_reserve` spends, once and for all, for `durableReserved r` (persistent: no durable name
  lies under `r/`); `durableOwnR r fs` is the files with the area `r` reserved. The specs take a
  mode `o` (`durableOwnM o`: `none` unreserved, `some r` reserved at `r`) and a name the mode allows
  (`durableNameOk o`: any while unreserved, a clean absolute path outside `r/` once reserved).
  Since the crash keeps the ghost names and no start resource re-mints the authority, a reservation
  holds for every later generation.
* The specs hold for any program whose extensions include the durable state
  (`HasExt durableExt`), with an injective encoding of strings as values.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.Ghost.GhostVar
public import Perennial.Golang.Defn.PostLang
public import Perennial.Ghost.GhostMap
public import GooseLang.Ext.Durable.Impl
public import GooseLang.Ext.AbsDisk.Paths

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Ghost state -/

/-- What the adequacy theorem provides: ghost variables. -/
class DurableGpreS (GF : BundledGFunctors) where
  durablePreAllG : AllG GF

/-- The ghost variable of the files, and the WAL area's reservation. -/
structure DurableGS (GF : BundledGFunctors) where
  durableAllG : AllG GF
  durableName : GName
  /-- The WAL area's reservation: a ghost map at key `()`, empty while unreserved. -/
  durableResvName : GName

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

/-- The reservation's authority at `m` (`∅`: unreserved). -/
def durableResvAuth (hL : DurableGS GF) (m : GMap Unit GoString) : IProp GF :=
  letI := hL.durableAllG
  ghostMapAuth hL.durableResvName 1 m

/-- The program's start: its half of the files `fs`, and the authority of the (empty)
reservation. -/
def durableStart (hL : DurableGS GF) (fs : DurableState) : IProp GF :=
  iprop(durableVar hL (1 : Qp).half fs ∗ durableResvAuth hL ∅)

theorem durable_local_init (hPre : DurableGpreS GF) (fs : DurableState) :
    ⊢@{IProp GF} |==> ∃ hL : DurableGS GF, durableCtx hL fs ∗ durableStart hL fs := by
  letI := hPre.durablePreAllG
  imod ghostVar_alloc (GF := GF) fs with ⟨%γ, H⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := GoString) with ⟨%γr, Hr⟩
  imodintro
  iexists (⟨hPre.durablePreAllG, γ, γr⟩ : DurableGS GF)
  unfold durableCtx durableStart durableResvAuth durableVar
  icases (ghostVar_split_half γ 1 fs).mp $$ H with ⟨H1, H2⟩
  iframe H1 H2
  iexact Hr

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
  localStart hL fs := durableStart hL fs
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

/-- The node's files are `fs`, and no area is reserved (the program's half, with the reservation's
authority: `durable_reserve` spends it). -/
def durableOwn (fs : DurableState) : IProp GF :=
  iprop(durableVar gooseDurableGS (1 : Qp).half fs ∗
    (letI := (gooseDurableGS (GF := GF)).durableAllG
     ghostMapAuth (gooseDurableGS (GF := GF)).durableResvName 1 (∅ : GMap Unit GoString)))

/-- **No durable name lies under `r/`, ever** (persistent; survives crashes: `durable_crash_interp`
keeps the ghost names). -/
def durableReserved (r : GoString) : IProp GF :=
  letI := (gooseDurableGS (GF := GF)).durableAllG
  () ↪[(gooseDurableGS (GF := GF)).durableResvName]□ r

/-- The files are `fs`, the area `r` reserved. -/
def durableOwnR (r : GoString) (fs : DurableState) : IProp GF :=
  iprop(durableVar gooseDurableGS (1 : Qp).half fs ∗ durableReserved r)

/-- The files are `fs`, in the mode `o`: unreserved (`none`), or the area `r` reserved
(`some r`). -/
def durableOwnM : Option GoString → DurableState → IProp GF
  | none => durableOwn
  | some r => durableOwnR r

/-- A name the mode allows: any while unreserved; reserved at `r`, a clean absolute path outside
`r/`. -/
def durableNameOk : Option GoString → GoString → Prop
  | none, _ => True
  | some r, n => cleanAbsPath n ∧ ¬ underDir r n

theorem durableOwnM_none : durableOwnM (L := L) none = durableOwn := rfl
theorem durableNameOk_none (n : GoString) : durableNameOk none n := trivial

instance durableOwn_timeless (fs : DurableState) : Timeless (durableOwn (L := L) fs) := by
  unfold durableOwn; infer_instance

instance durableReserved_persistent (r : GoString) : Persistent (durableReserved (L := L) r) := by
  unfold durableReserved; infer_instance

instance durableReserved_timeless (r : GoString) : Timeless (durableReserved (L := L) r) := by
  unfold durableReserved; infer_instance

instance durableOwnR_timeless (r : GoString) (fs : DurableState) :
    Timeless (durableOwnR (L := L) r fs) := by
  unfold durableOwnR; infer_instance

instance durableOwnM_timeless (o : Option GoString) (fs : DurableState) :
    Timeless (durableOwnM (L := L) o fs) := by
  cases o <;> unfold durableOwnM <;> infer_instance

/-- **Reserving the WAL area `r`**, once and for all: every file name is a clean absolute path
outside `r/`. -/
theorem durable_reserve (r : GoString) (fs : DurableState)
    (_h : ∀ k v, fs !! k = some v → cleanAbsPath k ∧ ¬ underDir r k) :
    ⊢ durableOwn (L := L) fs ==∗ durableOwnR r fs := by
  unfold durableOwn durableOwnR durableReserved
  letI := (gooseDurableGS (L := L)).durableAllG
  iintro ⟨Hv, Ha⟩
  imod ghost_map_insert_persist () r rfl $$ Ha with ⟨-, Hr⟩
  imodintro
  iframe Hv Hr

/-- One reserved area. -/
theorem durableReserved_agree (r r' : GoString) :
    ⊢ durableReserved (L := L) r -∗ durableReserved r' -∗ ⌜r = r'⌝ := by
  unfold durableReserved
  letI := (gooseDurableGS (L := L)).durableAllG
  iintro H1 H2
  icases ghostMapElem_agree () _ _ _ r r' $$ H1 H2 with %h
  ipureintro; exact h

/-- The program's half of the files, from either mode, and the way back. -/
theorem durableOwnM_var (o : Option GoString) (fs : DurableState) :
    ⊢@{IProp GF} durableOwnM (L := L) o fs -∗
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs ∗
      ∀ fs', durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs' -∗ durableOwnM o fs' := by
  cases o <;> simp only [durableOwnM]
  · unfold durableOwn
    iintro ⟨Hv, Ha⟩
    iframe Hv
    iintro %fs' Hv
    iframe Hv Ha
  · unfold durableOwnR
    iintro ⟨Hv, #Hr⟩
    iframe Hv
    iintro %fs' Hv
    iframe Hv Hr

theorem durable_local_ctx_eq (fs : DurableState) :
    ExtInterp.localCtx (E := durableExt) (extLocalGS durableExt) fs ⊣⊢
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs := .rfl

theorem durableVar_agreeM (o : Option GoString) (fs fs' : DurableState) :
    ⊢@{IProp GF} durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs -∗
      durableOwnM (L := L) o fs' -∗ ⌜fs = fs'⌝ := by
  iintro Hl Hown
  icases durableOwnM_var o fs' $$ Hown with ⟨Hv, -⟩
  unfold durableVar
  letI := (gooseDurableGS (L := L)).durableAllG
  iapply ghostVar_agree $$ Hl Hv

theorem durableVar_updateM (o : Option GoString) (fs fs' new : DurableState) :
    ⊢@{IProp GF} durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs -∗
      durableOwnM (L := L) o fs' ==∗
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half new ∗ durableOwnM (L := L) o new := by
  iintro Hl Hown
  icases durableOwnM_var o fs' $$ Hown with ⟨Hv, Hback⟩
  imod (show ⊢@{IProp GF} durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs -∗
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs' ==∗
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half new ∗
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half new by
    unfold durableVar
    letI := (gooseDurableGS (L := L)).durableAllG
    exact ghostVar_update_halves _ _ _ _) $$ Hl Hv with ⟨Hl, Hv⟩
  imodintro
  iframe Hl
  iapply Hback $$ Hv

theorem durableVar_agree (fs fs' : DurableState) :
    ⊢@{IProp GF} durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs -∗
      durableOwn (L := L) fs' -∗ ⌜fs = fs'⌝ :=
  durableVar_agreeM none fs fs'

theorem durableVar_update (fs fs' new : DurableState) :
    ⊢@{IProp GF} durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs -∗
      durableOwn (L := L) fs' ==∗
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half new ∗ durableOwn (L := L) new :=
  durableVar_updateM none fs fs' new

/-- `Read` as a logically atomic spec: the files' ownership is needed only during the step,
so it can come from an invariant. -/
theorem wp_DurableRead_atomic (o : Option GoString) (f : GoString) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ fs : DurableState, durableOwnM o fs ∗
      (durableOwnM o fs ={∅,E}=∗ Φ (durableReadResult fs f)))
    ⊢ WP (ExternalOp durableExt.name "Read" (Val (#f))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep "Read" (#f) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  imod HAU with ⟨%fs, Hown, Hclose⟩
  icases (durable_local_ctx_eq σ).mp $$ Hl with Hl
  icases durableVar_agreeM o σ fs $$ Hl Hown with %Heq
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

/-- `Write` as a logically atomic spec, of a name the mode allows (the premise is the caller's
obligation: the step itself writes any name). -/
theorem wp_DurableWrite_atomic (o : Option GoString) (f data : GoString)
    (_h : durableNameOk o f) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ fs : DurableState, durableOwnM o fs ∗
      (durableOwnM o (<[f := data]> fs) ={∅,E}=∗ Φ #()))
    ⊢ WP (ExternalOp durableExt.name "Write" (Val (PairV (#f) (#data)))) @ s; E
      {{ Φ }} := by
  iintro HAU
  iapply wp_extStep "Write" (PairV (#f) (#data)) Φ (by simp [val.isPanic])
  iintro %h %σ %g Hheap Hl Hg
  imod HAU with ⟨%fs, Hown, Hclose⟩
  icases (durable_local_ctx_eq σ).mp $$ Hl with Hl
  icases durableVar_agreeM o σ fs $$ Hl Hown with %Heq
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
  imod durableVar_updateM o σ σ (<[f := data]> σ) $$ Hl Hown with ⟨Hl, Hown⟩
  imod Hclose $$ Hown with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (durable_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iexact HΦ

theorem wp_DurableRead (f : GoString) (fs : DurableState) :
    {{ (durableOwn fs : IProp GF) }} (ExternalOp durableExt.name "Read" (Val (#f)))
      @ s; E
    {{ RET (durableReadResult fs f); durableOwn fs }} := by
  iintro %Φ Hown HΦ
  iapply wp_extStep "Read" (#f) Φ (by simp)
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
      (ExternalOp durableExt.name "Write" (Val (PairV (#f) (#data)))) @ s; E
    {{ RET #(); durableOwn (<[f := data]> fs) }} := by
  iintro %Φ Hown HΦ
  iapply wp_extStep "Write" (PairV (#f) (#data)) Φ (by simp [val.isPanic])
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
extension named `durableExt.name`, with its semantics and ghost state. Not an instance (it holds
only under `durableExts`): a closed theorem makes it a local one. -/
theorem durableExts_hasExt : HasExt durableExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

end closed

end Perennial
