/-
Iris reasoning principles for the issue-record extension (`Impl.lean`; the restart plan's R2c stage
2, 2026-11-02): the durable-state extension's (`GooseLang/Ext/Durable/Specs.lean`) for a map from ids
to generators.

* The ghost state: a ghost map of the record, its authority and every entry's persistent element in
  the state interpretation. The program owns nothing of it at the start (its start resource is
  `True`, so a `Main` takes nothing for it); it learns facts: `idIssueFrag id g`, `g` issued `id`
  (persistent; one issuer per id, `idIssueFrag_agree`), and, after a crash (`Crash.lean`),
  `idIssuePast id`, an earlier incarnation issued `id` (exclusive with every `idIssueFrag id g`,
  `idIssueFrag_past`).
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

/-- **The record's entry `id ↦ v`** (persistent): the ghost map's element. -/
def idIssueElemAt (hL : IdIssueGS GF) (id : w64) (v : Option Loc) : IProp GF :=
  letI := hL.idIssueAllG
  id ↪[hL.idIssueName]□ v

instance idIssueElemAt_persistent (hL : IdIssueGS GF) (id : w64) (v : Option Loc) :
    Persistent (idIssueElemAt hL id v) := by
  unfold idIssueElemAt; infer_instance

/-- **`id` was issued by the generator `g`** (persistent; of the incarnation of `hL`). -/
def idIssueFragAt (hL : IdIssueGS GF) (id : w64) (g : Loc) : IProp GF :=
  idIssueElemAt hL id (some g)

instance idIssueFragAt_persistent (hL : IdIssueGS GF) (id : w64) (g : Loc) :
    Persistent (idIssueFragAt hL id g) := by
  unfold idIssueFragAt; infer_instance

/-- **`id` was issued by an earlier incarnation** (persistent; before a crash of the machine, as seen
by the incarnation of `hL`: `Crash.lean`). -/
def idIssuePastAt (hL : IdIssueGS GF) (id : w64) : IProp GF :=
  idIssueElemAt hL id none

instance idIssuePastAt_persistent (hL : IdIssueGS GF) (id : w64) :
    Persistent (idIssuePastAt hL id) := by
  unfold idIssuePastAt; infer_instance

/-- **No generator of an incarnation issues an id an earlier one issued.** -/
theorem idIssueFragAt_past (hL : IdIssueGS GF) (id : w64) (g : Loc) :
    ⊢@{IProp GF} idIssueFragAt hL id g -∗ idIssuePastAt hL id -∗ False := by
  unfold idIssueFragAt idIssuePastAt idIssueElemAt
  letI := hL.idIssueAllG
  iintro #H1 #H2
  ihave %H := ghostMapElem_agree $$ H1 H2
  cases H

/-- The interpretation of the record `M`: a ghost record `Mg`, part of it (the entries made during
the run: any initial record is allowed, and the ghost one starts empty; after a crash, the entries
made before it, as an earlier incarnation's), its authority and every entry's persistent element. -/
def idIssueCtx (hL : IdIssueGS GF) (M : IdIssueState) : IProp GF :=
  letI := hL.idIssueAllG
  iprop(∃ Mg : IdIssueState, ghostMapAuth hL.idIssueName 1 Mg ∗
    ([∗map] id ↦ v ∈ Mg, idIssueElemAt hL id v) ∗ ⌜∀ id v, Mg !! id = some v → M !! id = some v⌝)

/-- **The incarnation `hL` crashed** (T10 B6 (b), 2026-11-26): its record's authority, which only the
crash's rest hands over (`Crash.lean`'s `idIssueCrashStart`); while the incarnation runs, its state
interpretation holds it (`idIssueCtx_dead`). An invariant of the incarnation's facts is cancelled by
depositing it. -/
def idIssueDeadAt (hL : IdIssueGS GF) : IProp GF :=
  letI := hL.idIssueAllG
  iprop(∃ Mg : IdIssueState, ghostMapAuth hL.idIssueName 1 Mg)

instance idIssueDeadAt_timeless (hL : IdIssueGS GF) : Timeless (idIssueDeadAt hL) := by
  unfold idIssueDeadAt; infer_instance

/-- **A running incarnation has not crashed.** -/
theorem idIssueCtx_dead (hL : IdIssueGS GF) (M : IdIssueState) :
    ⊢@{IProp GF} idIssueCtx hL M -∗ idIssueDeadAt hL -∗ False := by
  letI := hL.idIssueAllG
  iintro HM Hd
  iunfold idIssueCtx at HM
  icases HM with ⟨%Mg, HA, -, -⟩
  iunfold idIssueDeadAt at Hd
  icases Hd with ⟨%Mg', HA'⟩
  ihave %H := ghostMapAuth_valid_2 hL.idIssueName 1 1 Mg Mg' $$ HA HA'
  exact absurd H.1 (by decide)

theorem idIssue_local_init (hPre : IdIssueGpreS GF) (M : IdIssueState) :
    ⊢@{IProp GF} |==> ∃ hL : IdIssueGS GF, idIssueCtx hL M ∗ iprop(True) := by
  letI := hPre.idIssuePreAllG
  imod (ghost_map_alloc_empty (GF := GF) (K := w64) (V := Option Loc)) with ⟨%γ, H⟩
  imodintro
  iexists (⟨hPre.idIssuePreAllG, γ⟩ : IdIssueGS GF)
  unfold idIssueCtx
  isplitl
  · iexists ∅
    iframe H
    isplitl
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · ipureintro; intro id v h; simp [GMap.lookup_empty] at h
  · itrivial

/-- **The record's step** (ghost): the record after an `"Issue"` of `(id, g)`, and, if it is
allowed, the id's element. -/
theorem idIssue_ghost_step (hL : IdIssueGS GF) (M : IdIssueState) (id : w64) (g : Loc) :
    ⊢@{IProp GF} idIssueCtx hL M ==∗
      idIssueCtx hL (idIssueNext M id g) ∗ (⌜idIssueOk M id g = true⌝ → idIssueFragAt hL id g) := by
  letI := hL.idIssueAllG
  iintro HM
  iunfold idIssueCtx at HM
  icases HM with ⟨%Mg, HA, #HE, %Hsub⟩
  by_cases hok : idIssueOk M id g = true
  · -- allowed: the physical record has no other generator's entry, so the ghost one has none
    have hM : M !! id = none ∨ M !! id = some (some g) := by
      unfold idIssueOk at hok
      cases h : M !! id with
      | none => exact Or.inl rfl
      | some o =>
        rw [h] at hok
        cases o with
        | none => simp at hok
        | some g' => simp at hok; exact Or.inr (by rw [hok])
    have hnext : idIssueNext M id g = M.insert id (some g) := by unfold idIssueNext; rw [hok]; rfl
    rw [hnext]
    cases hg : Mg !! id with
    | none =>
      imod ghost_map_insert_persist id (some g) hg $$ HA with ⟨HA, #He⟩
      imodintro
      isplitl [HA]
      · iunfold idIssueCtx
        iexists (Mg.insert id (some g))
        iframe HA
        isplitl
        · iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (m := Mg)
            (Φ := fun i v => idIssueElemAt hL i v) hg).2
          iframe HE
          iunfold idIssueElemAt; iexact He
        · ipureintro
          intro i v h
          rw [GMap.lookup_insert_eq_iff] at h ⊢
          by_cases hi : id = i
          · simp only [hi, ite_true] at h ⊢; exact h
          · simp only [hi, ite_false] at h ⊢; exact Hsub i v h
      · iintro -; iunfold idIssueFragAt; iunfold idIssueElemAt; iexact He
    | some v' =>
      have hg' : v' = some g := by
        have := Hsub id v' hg
        rcases hM with h | h <;> rw [h] at this <;> cases this; rfl
      subst hg'
      icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := Mg)
        (Φ := fun i v => idIssueElemAt hL i v) hg).1 $$ HE with ⟨#He, -⟩
      imodintro
      isplitl [HA]
      · iunfold idIssueCtx
        iexists Mg
        iframe HA HE
        ipureintro
        intro i v'' h
        rw [GMap.lookup_insert_eq_iff]
        by_cases hi : id = i
        · subst hi; rw [hg] at h; cases h; simp
        · simp only [hi, ite_false]; exact Hsub i v'' h
      · iintro -; iunfold idIssueFragAt; iexact He
  · -- refused: nothing changes
    have hnext : idIssueNext M id g = M := by
      unfold idIssueNext; rw [if_neg hok]
    rw [hnext]
    imodintro
    isplitl [HA]
    · iunfold idIssueCtx
      iexists Mg
      iframe HA HE
      ipureintro; exact Hsub
    · iintro %h; exact absurd h hok

end ghost

/-- The ghost state of the issue record. The program starts with nothing, whatever the initial
record: its facts come from `"Issue"`. -/
instance idIssue_interp : ExtInterp idIssueExt where
  LocalGS := IdIssueGS
  GlobalGS _ := Unit
  localCtx := idIssueCtx
  globalCtx _ _ := iprop(True)
  PreG := IdIssueGpreS
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart _ _ := iprop(True)
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre M _ _ := idIssue_local_init hPre M

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

/-- **`id` was issued by an earlier incarnation of the machine** (persistent; the program's fact after a
crash, `Crash.lean`'s `idIssueCrashStart_past`). -/
def idIssuePast (id : w64) : IProp GF := idIssuePastAt (gooseIdIssueGS (L := L)) id

instance idIssuePast_persistent (id : w64) : Persistent (idIssuePast (L := L) id) := by
  unfold idIssuePast; infer_instance

/-- **No generator of this incarnation issues an id an earlier one issued.** -/
theorem idIssueFrag_past (id : w64) (g : Loc) :
    ⊢@{IProp GF} idIssueFrag (L := L) id g -∗ idIssuePast (L := L) id -∗ False :=
  idIssueFragAt_past _ id g

/-- **One issuer per id.** -/
theorem idIssueFrag_agree (id : w64) (g g' : Loc) :
    ⊢@{IProp GF} idIssueFrag (L := L) id g -∗ idIssueFrag (L := L) id g' -∗ ⌜g = g'⌝ := by
  unfold idIssueFrag idIssueFragAt idIssueElemAt
  letI := (gooseIdIssueGS (L := L)).idIssueAllG
  iintro #H1 #H2
  ihave %H := ghostMapElem_agree $$ H1 H2
  ipureintro; cases H; rfl

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

/-- **`"Issue"`, for a step that may find its incarnation crashed** (T10 B6 (b)): as `wp_IdIssue`, but
the update may give up with `idIssueDeadAt` of the step's own incarnation (from a cancelled invariant
it opened), which the step refutes with its state interpretation's authority. -/
theorem wp_IdIssue_live (id : w64) (g : Loc) (Φ : val → IProp GF) :
    (|={E,∅}=> idIssueDeadAt (gooseIdIssueGS (L := L)) ∨
      ∀ b : Bool, (⌜b = true⌝ → idIssueFrag (L := L) id g) ={∅,E}=∗ Φ #b)
    ⊢ WP (ExternalOp idIssueExt.name "Issue" (Val (PairV (#id) (#g)))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep "Issue" (PairV (#id) (#g)) Φ (by simp [val.isPanic])
  iintro %h %σ %gs Hheap Hl Hg
  imod HAU with Hclose
  icases (idIssue_local_ctx_eq σ).mp $$ Hl with Hl
  icases Hclose with (Hd | Hclose)
  · iexfalso
    iapply idIssueCtx_dead _ σ $$ Hl Hd
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
  · unfold idIssueFrag idIssueFragAt idIssueElemAt; infer_instance
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

open Classical in
/-- **`id` was issued by an earlier incarnation, read without the instance** (T10 B6 (b)). -/
noncomputable def idIssuePastD (id : w64) : IProp GF :=
  if h : HasExt idIssueExt then (haveI := h; idIssuePast (L := L) id) else iprop(False)

instance idIssuePastD_persistent (id : w64) : Persistent (idIssuePastD (L := L) id) := by
  unfold idIssuePastD; split <;> infer_instance

instance idIssuePastD_timeless (id : w64) : Timeless (idIssuePastD (L := L) id) := by
  unfold idIssuePastD; split
  · unfold idIssuePast idIssuePastAt idIssueElemAt; infer_instance
  · infer_instance

theorem idIssuePastD_eq [h : HasExt idIssueExt] (id : w64) :
    idIssuePastD (L := L) id = idIssuePast (L := L) id := by
  unfold idIssuePastD; rw [dif_pos h]

/-- An id this incarnation's generator issued is not an earlier incarnation's. -/
theorem idIssueFragD_pastD (id : w64) (g : Loc) :
    ⊢@{IProp GF} idIssueFragD (L := L) id g -∗ idIssuePastD (L := L) id -∗ False := by
  by_cases h : HasExt idIssueExt
  · haveI := h
    rw [idIssueFragD_eq, idIssuePastD_eq]
    exact idIssueFrag_past id g
  · unfold idIssueFragD; rw [dif_neg h]
    iintro H; iexfalso; iexact H

open Classical in
/-- **This incarnation crashed, read without the instance** (T10 B6 (b); `idIssueDeadAt`). -/
noncomputable def idIssueDeadD : IProp GF :=
  if h : HasExt idIssueExt then (haveI := h; idIssueDeadAt (gooseIdIssueGS (L := L))) else iprop(False)

instance idIssueDeadD_timeless : Timeless (idIssueDeadD (L := L)) := by
  unfold idIssueDeadD; split <;> infer_instance

theorem idIssueDeadD_eq [h : HasExt idIssueExt] :
    idIssueDeadD (L := L) = idIssueDeadAt (gooseIdIssueGS (L := L)) := by
  unfold idIssueDeadD; rw [dif_pos h]

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
