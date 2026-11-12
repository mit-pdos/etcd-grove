/-
Iris reasoning principles for the durable-state extension.

Notes:
* The ghost state is one ghost variable holding all the files (`durableOwn fs`, `fs` the map
  from names to contents), half of it in the state interpretation and half the program's:
  unlike points-to facts per file, it says which files do not exist, which a read returns.
  A program that shares the files puts `durableOwn` in an invariant (the atomic specs). Its crash
  interpretation (`Crash.lean`) keeps the ghost names.
* The WAL area's reservation (WAL W4a revision, 2026-11-11; in the state interpretation since its
  second round, 2026-11-12): a second ghost name holds a ghost map at the one key `()`, its
  authority in the state interpretation (`durableCtx`), with the invariant that once the key holds
  `some r` every file name is one the reserved mode allows (`durableResvInv`). The program holds
  the key's element: `() ↪ none` (exclusive) while unreserved (`durableOwn fs`), `() ↪□ some r`
  once reserved (`durableReserved r`, persistent; `durableOwnR r fs`). The reservation is made
  inside a durable step (`wp_DurableRead_atomic`'s mode change `durableModeStep`), which sees the
  interpretation, so its condition (every current name allowed) is checked against the real files;
  every `Write` step re-establishes the invariant, so a reserved-mode write of a name the mode does
  not allow has no proof, whatever lemma it uses. The specs take a mode `o` (`durableOwnM o`:
  `none` unreserved, `some r` reserved at `r`) and a name the mode allows (`durableNameOk o`: any
  while unreserved; once reserved, a clean absolute path outside `r/` whose last element does not
  start with `.`, so never `TouchDirAll`'s probe `d/.touch` nor durable's own temporaries). Since
  the crash keeps the ghost names and no start resource re-mints the element `() ↪ none`, a
  reservation holds for every later generation.
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
  /-- The WAL area's reservation: a ghost map at key `()`, `none` while unreserved. -/
  durableResvName : GName

section durable
variable {GF : BundledGFunctors}

/-- The files are `fs`, with fraction `q` (a half is the program's, a half the state
interpretation's). -/
def durableVar (hL : DurableGS GF) (q : Qp) (fs : DurableState) : IProp GF :=
  letI := hL.durableAllG
  ghostVar hL.durableName q fs

/-- **The name `n` hides**: its last element starts with `.` (`TouchDirAll`'s probe `d/.touch`,
durable's own temporaries). -/
def durableHidden (n : GoString) : Prop :=
  ∃ p c : GoString, n = p ++ go!"/." ++ c ∧ W8 47 ∉ c

/-- A name the mode allows: any while unreserved; reserved at `r`, a clean absolute path outside
`r/` that does not hide. -/
def durableNameOk : Option GoString → GoString → Prop
  | none, _ => True
  | some r, n => cleanAbsPath n ∧ ¬ underDir r n ∧ ¬ durableHidden n

/-- **The reservation's invariant**: once the area `r` is reserved, every file name is one the
reserved mode allows. -/
def durableResvInv (m : GMap Unit (Option GoString)) (fs : DurableState) : Prop :=
  ∀ r, m !! () = some (some r) → ∀ k v, fs !! k = some v → durableNameOk (some r) k

/-- The reservation's authority at `m`, with its invariant over the files `fs`. -/
def durableResvAuth (hL : DurableGS GF) (fs : DurableState) : IProp GF :=
  letI := hL.durableAllG
  iprop(∃ m : GMap Unit (Option GoString), ghostMapAuth hL.durableResvName 1 m ∗
    ⌜durableResvInv m fs⌝)

/-- The interpretation of the files: their other half, and the reservation's authority with its
invariant. -/
def durableCtx (hL : DurableGS GF) (fs : DurableState) : IProp GF :=
  iprop(durableVar hL (1 : Qp).half fs ∗ durableResvAuth hL fs)

instance durableVar_timeless (hL : DurableGS GF) (q : Qp) (fs : DurableState) :
    Timeless (durableVar hL q fs) := by
  unfold durableVar; infer_instance

/-- The program's start: its half of the files `fs`, and the reservation's element, unreserved. -/
def durableStart (hL : DurableGS GF) (fs : DurableState) : IProp GF :=
  letI := hL.durableAllG
  iprop(durableVar hL (1 : Qp).half fs ∗ () ↪[hL.durableResvName] (none : Option GoString))

theorem durable_local_init (hPre : DurableGpreS GF) (fs : DurableState) :
    ⊢@{IProp GF} |==> ∃ hL : DurableGS GF, durableCtx hL fs ∗ durableStart hL fs := by
  letI := hPre.durablePreAllG
  imod ghostVar_alloc (GF := GF) fs with ⟨%γ, H⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := Option GoString) with ⟨%γr, Hr⟩
  imod ghost_map_insert (GF := GF) () (none : Option GoString) (GMap.lookup_empty _) $$ Hr
    with ⟨Hr, He⟩
  imodintro
  iexists (⟨hPre.durablePreAllG, γ, γr⟩ : DurableGS GF)
  unfold durableCtx durableStart durableResvAuth durableVar
  icases (ghostVar_split_half γ 1 fs).mp $$ H with ⟨H1, H2⟩
  iframe H1 H2 He
  iexists _
  iframe Hr
  ipureintro
  intro r hr
  simp [GMap.lookup_insert_eq_iff] at hr

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
element at `none`: a durable step's mode change spends it, `durableModeStep`). -/
def durableOwn (fs : DurableState) : IProp GF :=
  iprop(durableVar gooseDurableGS (1 : Qp).half fs ∗
    (letI := (gooseDurableGS (GF := GF)).durableAllG
     () ↪[(gooseDurableGS (GF := GF)).durableResvName] (none : Option GoString)))

/-- **The area `r` is reserved, for good**: every durable name is one the reserved mode allows (a
clean absolute path outside `r/` that does not hide; the interpretation's invariant,
`durableResvInv`). Persistent; survives crashes (`durable_crash_interp` keeps the ghost names). -/
def durableReserved (r : GoString) : IProp GF :=
  letI := (gooseDurableGS (GF := GF)).durableAllG
  () ↪[(gooseDurableGS (GF := GF)).durableResvName]□ (some r)

/-- The files are `fs`, the area `r` reserved. -/
def durableOwnR (r : GoString) (fs : DurableState) : IProp GF :=
  iprop(durableVar gooseDurableGS (1 : Qp).half fs ∗ durableReserved r)

/-- The files are `fs`, in the mode `o`: unreserved (`none`), or the area `r` reserved
(`some r`). -/
def durableOwnM : Option GoString → DurableState → IProp GF
  | none => durableOwn
  | some r => durableOwnR r

/-- **The mode may go from `o` to `o'`** at a step on the files `fs`: it stays, or an unreserved
mode reserves an area when every current name is one the reserved mode allows. -/
def durableModeStep (o o' : Option GoString) (fs : DurableState) : Prop :=
  o' = o ∨ (o = none ∧ ∀ k v, fs !! k = some v → durableNameOk o' k)

theorem durableModeStep_refl (o : Option GoString) (fs : DurableState) :
    durableModeStep o o fs := Or.inl rfl

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

/-- One reserved area. -/
theorem durableReserved_agree (r r' : GoString) :
    ⊢ durableReserved (L := L) r -∗ durableReserved r' -∗ ⌜r = r'⌝ := by
  unfold durableReserved
  letI := (gooseDurableGS (L := L)).durableAllG
  iintro H1 H2
  icases ghostMapElem_agree () _ _ _ (some r) (some r') $$ H1 H2 with %h
  ipureintro; exact Option.some.inj h

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
      durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs ∗
      durableResvAuth (gooseDurableGS (L := L)) fs := .rfl

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

/-- **A write keeps the reservation's invariant**, for a name the mode allows: the mode's element
fixes the key `()` (`none`, or `some r`). -/
theorem durableResvAuth_insert (o : Option GoString) (fs fs0 : DurableState) (f data : GoString)
    (h : durableNameOk o f) :
    ⊢@{IProp GF} durableResvAuth (gooseDurableGS (L := L)) fs -∗ durableOwnM (L := L) o fs0 -∗
      durableResvAuth (gooseDurableGS (L := L)) (<[f := data]> fs) ∗ durableOwnM (L := L) o fs0 := by
  letI := (gooseDurableGS (L := L)).durableAllG
  unfold durableResvAuth
  iintro ⟨%m, HA, %Hinv⟩ Hown
  cases o with
  | none =>
    simp only [durableOwnM]
    unfold durableOwn
    icases Hown with ⟨Hv, He⟩
    icases ghost_map_lookup $$ HA He with %Hl
    iframe Hv He
    iexists m
    iframe HA
    ipureintro
    intro r hr
    have : m !! () = some none := Hl
    rw [this] at hr; cases hr
  | some r =>
    simp only [durableOwnM]
    unfold durableOwnR durableReserved
    icases Hown with ⟨Hv, #He⟩
    icases ghost_map_lookup $$ HA He with %Hl
    iframe Hv He
    iexists m
    iframe HA
    ipureintro
    intro r' hr' k v hk
    have hm : m !! () = some (some r) := Hl
    rw [hm] at hr'
    obtain rfl : r = r' := Option.some.inj (Option.some.inj hr')
    rw [GMap.lookup_insert_Some] at hk
    rcases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
    · exact h
    · exact Hinv r hm k v hk

/-- **A mode change at a step** (`durableModeStep`): reserving the area `r` spends the unreserved
element, given that every current name is one the reserved mode allows; the interpretation's
invariant then holds of the same files. -/
theorem durableOwnM_step (o o' : Option GoString) (fs : DurableState)
    (h : durableModeStep o o' fs) :
    ⊢@{IProp GF} durableResvAuth (gooseDurableGS (L := L)) fs -∗ durableOwnM (L := L) o fs ==∗
      durableResvAuth (gooseDurableGS (L := L)) fs ∗ durableOwnM (L := L) o' fs := by
  iintro HA Hown
  rcases h with rfl | ⟨rfl, hok⟩
  · imodintro; iframe HA Hown
  cases o' with
  | none => imodintro; iframe HA Hown
  | some r =>
    letI := (gooseDurableGS (L := L)).durableAllG
    simp only [durableOwnM]
    unfold durableResvAuth durableOwn durableOwnR durableReserved
    icases HA with ⟨%m, HA, %Hinv⟩
    icases Hown with ⟨Hv, He⟩
    imod ghost_map_update (some r) $$ HA He with ⟨HA, He⟩
    imod ghostMapElem_persist $$ He with #He
    imodintro
    iframe Hv He
    iexists _
    iframe HA
    ipureintro
    intro r' hr' k v hk
    rw [GMap.lookup_insert] at hr'
    obtain rfl : r = r' := Option.some.inj (Option.some.inj hr')
    exact hok k v hk

/-- `Read` as a logically atomic spec: the files' ownership is needed only during the step,
so it can come from an invariant. The step may change the mode (`durableModeStep`: an unreserved
program reserves the WAL area here, at a step, where the reservation sees the real files). -/
theorem wp_DurableRead_atomic (o o' : Option GoString) (f : GoString) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ fs : DurableState, durableOwnM o fs ∗ ⌜durableModeStep o o' fs⌝ ∗
      (durableOwnM o' fs ={∅,E}=∗ Φ (durableReadResult fs f)))
    ⊢ WP (ExternalOp durableExt.name "Read" (Val (#f))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep "Read" (#f) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  imod HAU with ⟨%fs, Hown, %Hmode, Hclose⟩
  icases (durable_local_ctx_eq σ).mp $$ Hl with ⟨Hl, HR⟩
  icases durableVar_agreeM o σ fs $$ Hl Hown with %Heq
  subst Heq
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, σ, g, rfl, f, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, f', Hv, rfl, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj Hv
  imod durableOwnM_step o o' _ Hmode $$ HR Hown with ⟨HR, Hown⟩
  imod Hclose $$ Hown with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl HR]
  · iapply (durable_local_ctx_eq _).mpr; iframe Hl HR
  iapply wp_value'
  iexact HΦ

/-- `Write` as a logically atomic spec, of a name the mode allows (the premise is what keeps the
interpretation's reservation invariant, `durableResvAuth_insert`). -/
theorem wp_DurableWrite_atomic (o : Option GoString) (f data : GoString)
    (hf : durableNameOk o f) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ fs : DurableState, durableOwnM o fs ∗
      (durableOwnM o (<[f := data]> fs) ={∅,E}=∗ Φ #()))
    ⊢ WP (ExternalOp durableExt.name "Write" (Val (PairV (#f) (#data)))) @ s; E
      {{ Φ }} := by
  iintro HAU
  iapply wp_extStep "Write" (PairV (#f) (#data)) Φ (by simp [val.isPanic])
  iintro %h %σ %g Hheap Hl Hg
  imod HAU with ⟨%fs, Hown, Hclose⟩
  icases (durable_local_ctx_eq σ).mp $$ Hl with ⟨Hl, HR⟩
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
  icases durableResvAuth_insert o σ σ f data hf $$ HR Hown with ⟨HR, Hown⟩
  imod durableVar_updateM o σ σ (<[f := data]> σ) $$ Hl Hown with ⟨Hl, Hown⟩
  imod Hclose $$ Hown with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl HR]
  · iapply (durable_local_ctx_eq _).mpr; iframe Hl HR
  iapply wp_value'
  iexact HΦ

theorem wp_DurableRead (f : GoString) (fs : DurableState) :
    {{ (durableOwn fs : IProp GF) }} (ExternalOp durableExt.name "Read" (Val (#f)))
      @ s; E
    {{ RET (durableReadResult fs f); durableOwn fs }} := by
  iintro %Φ Hown HΦ
  iapply wp_extStep "Read" (#f) Φ (by simp)
  iintro %h %σ %g Hheap Hl Hg
  icases (durable_local_ctx_eq σ).mp $$ Hl with ⟨Hl, HR⟩
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
  isplitl [Hl HR]
  · iapply (durable_local_ctx_eq _).mpr; iframe Hl HR
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
  icases (durable_local_ctx_eq σ).mp $$ Hl with ⟨Hl, HR⟩
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
  rw [← durableOwnM_none]
  icases durableResvAuth_insert none σ σ f data trivial $$ HR Hown with ⟨HR, Hown⟩
  imod durableVar_updateM none σ σ (<[f := data]> σ) $$ Hl Hown with ⟨Hl, Hown⟩
  imod Hclose
  imodintro
  iframe Hheap Hg
  isplitl [Hl HR]
  · iapply (durable_local_ctx_eq _).mpr; iframe Hl HR
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
