/-
The SMR invariant's execution step (package `laws`): executing one id of a slot while the SMR
invariant is open, committing the atomic update of a request executed for the first time.
The pure part (`ExecInv`, preserved by `execOne`) and the ghost part (`exec_one`, `exec_ids`).
-/
module

public import Dsverify.Proof.raxos.Ghost
public import Dsverify.Proof.raxos.Smr.Exec
public import Dsverify.Proof.raxos.Smr.SumId

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode BigSepM BigSepL Net
open Perennial.raxos.pure

/-! ## The pure state of an execution under the invariant -/

/-- The batches of the registry. -/
abbrev regB (Reg : GMap GoString RegEntry) : GoString → Option Batch :=
  fun y => (Reg !! y).map (RegEntry.batch y)

/-- The registry's facts the execution uses. -/
def RegOk (Reg : GMap GoString RegEntry) : Prop :=
  (∀ x e, Reg !! x = some e → e = RegEntry.nil → x = go!"nil") ∧
  (∀ x c j inp q t, Reg !! x = some (.op c j inp q t) → inputOk inp) ∧
  (∀ x, Reg !! x = some RegEntry.sum → cmdPut x = none)

/-- The invariant's facts about an execution state `es` and the outputs `Res`. -/
structure ExecInv (Reg : GMap GoString RegEntry) (Res : GMap GoString (KOut))
    (es : ExecSt) : Prop where
  res_iff : ∀ x, (Res !! x).isSome ↔ (∃ c j inp q tok, Reg !! x = some (.op c j inp q tok)) ∧
    x ∈ es.done
  res_ok : ∀ x o, Res !! x = some o → ∃ c j inp q tok, Reg !! x = some (.op c j inp q tok) ∧
    es.results x = some [ansOf inp o] ∧
    ∀ v, o = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil"
  store : storeOk es
  puts_good : ∀ p ∈ es.puts, goodVal p.2
  done_ok : ∀ x ∈ es.done, ∃ e, Reg !! x = some e ∧ msg.batchFit (e.batch x)

theorem execOne_old (B : GoString → Option Batch) (es : ExecSt) (x : GoString)
    (h : x ∈ es.done) : execOne B es x = es := by
  simp [execOne, h]

theorem execOne_new (B : GoString → Option Batch) (es : ExecSt) (x : GoString) (b : Batch)
    (h : x ∉ es.done) (hb : B x = some b) :
    execOne B es x = ⟨(execBatch es.store b.cmds).1, es.done ++ [x],
      fun y => if y = x then some (execBatch es.store b.cmds).2 else es.results y,
      es.puts ++ b.cmds.filterMap cmdPut⟩ := by
  simp [execOne, h, hb]

/-- An entry with no puts and no output (`"nil"`, a summary) executed. -/
theorem execInv_plain (Reg : GMap GoString RegEntry) (Res : GMap GoString (KOut))
    (es : ExecSt) (x : GoString) (e : RegEntry) (hI : ExecInv Reg Res es) (hx : x ∉ es.done)
    (hRx : Reg !! x = some e) (hnop : ∀ c j inp q tok, e ≠ .op c j inp q tok)
    (hputs : (e.batch x).cmds.filterMap cmdPut = []) (hb : msg.batchFit (e.batch x)) :
    ExecInv Reg Res (execOne (regB Reg) es x) ∧
      (execOne (regB Reg) es x).puts = es.puts := by
  have hB : regB Reg x = some (e.batch x) := by simp [regB, hRx]
  rw [execOne_new _ es x _ hx hB]
  have hnop' : ¬ ∃ c j inp q tok, Reg !! x = some (.op c j inp q tok) := by
    rintro ⟨c, j, inp, q, tok, h⟩; rw [hRx] at h; cases h; exact hnop c j inp q tok rfl
  have hnone : Res !! x = none := by
    cases h : Res !! x with
    | none => rfl
    | some o => exact absurd ((hI.res_iff x).1 (by simp [h])).1 hnop'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by simp [hputs]⟩
  · intro y
    rw [hI.res_iff y]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inl h2⟩
    · rintro ⟨h1, h2 | rfl⟩
      · exact ⟨h1, h2⟩
      · exact absurd h1 hnop'
  · intro y o hy
    obtain ⟨c, j, inp, q, tok, h1, h2, h3⟩ := hI.res_ok y o hy
    have : y ≠ x := by rintro rfl; rw [hnone] at hy; cases hy
    exact ⟨c, j, inp, q, tok, h1, by simp [this, h2], h3⟩
  · have := hI.store
    unfold storeOk at this ⊢
    simp only [this]
    rw [execBatch_store, hputs, List.append_nil]
  · intro p hp
    simp only [hputs, List.append_nil] at hp
    exact hI.puts_good p hp
  · intro y hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hI.done_ok y hy
    · exact ⟨_, hRx, hb⟩

/-- The new execution state of a request's batch executed for the first time. -/
theorem execOne_op (Reg : GMap GoString RegEntry) (es : ExecSt) (x : GoString) (c j : Nat)
    (inp : KIn) (q tok : GName) (hx : x ∉ es.done)
    (hRx : Reg !! x = some (.op c j inp q tok)) :
    execOne (regB Reg) es x = ⟨(execCmd es.store (cmdOf inp)).1, es.done ++ [x],
      fun y => if y = x then some [(execCmd es.store (cmdOf inp)).2] else es.results y,
      es.puts ++ [cmdOf inp].filterMap cmdPut⟩ := by
  have hB : regB Reg x = some ⟨x, clientName c, [cmdOf inp]⟩ := by
    simp [regB, hRx, RegEntry.batch]
  rw [execOne_new _ es x _ hx hB]
  rfl

theorem execInv_op (Reg : GMap GoString RegEntry) (Res : GMap GoString (KOut))
    (es : ExecSt) (x : GoString) (c j : Nat) (inp : KIn) (q tok : GName)
    (o : KOut) (hI : ExecInv Reg Res es) (hx : x ∉ es.done)
    (hRx : Reg !! x = some (.op c j inp q tok)) (hinp : inputOk inp)
    (hb : msg.batchFit (RegEntry.batch x (.op c j inp q tok)))
    (ho : (kvB.step inp es.store).2 = o) :
    ExecInv Reg (<[x := o]> Res) (execOne (regB Reg) es x) := by
  have hans : (execCmd es.store (cmdOf inp)).2 = ansOf inp o := by
    rw [(execCmd_step es.store inp hinp).2, ho]
  rw [execOne_op Reg es x c j inp q tok hx hRx]
  have hnone : Res !! x = none := by
    cases h : Res !! x with
    | none => rfl
    | some o' => exact absurd ((hI.res_iff x).1 (by simp [h])).2 hx
  -- the output's value, if any, is a good one
  have hgood : ∀ v, o = ⟨true, v⟩ → goodVal v := by
    intro v hv
    subst ho
    obtain ⟨put, k, v'⟩ := inp
    cases put with
    | true => simp [kvB] at hv
    | false =>
      simp only [kvB, Bool.false_eq_true, ite_false] at hv
      cases hk : es.store k with
      | none => rw [hk] at hv; cases hv
      | some w =>
        rw [hk] at hv
        cases hv
        have hst := hI.store
        unfold storeOk at hst
        rw [hst] at hk
        have hm := kvAbs_mem _ _ _ hk
        exact hI.puts_good _ (List.mem_reverse.1 hm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : y = x
    · subst hy
      simp only [GMap.lookup_insert, Option.isSome_some, true_iff]
      exact ⟨⟨c, j, inp, q, tok, hRx⟩, by simp⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hy), hI.res_iff y]
      simp [hy]
  · intro y o' hy'
    by_cases hy : y = x
    · subst hy
      rw [GMap.lookup_insert] at hy'
      cases hy'
      refine ⟨c, j, inp, q, tok, hRx, by simp [hans], ?_⟩
      intro v hv; exact hgood v hv
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hy)] at hy'
      obtain ⟨c', j', inp', q', tok', h1, h2, h3⟩ := hI.res_ok y o' hy'
      exact ⟨c', j', inp', q', tok', h1, by simp [hy, h2], h3⟩
  · have := hI.store
    unfold storeOk at this ⊢
    simp only [this]
    exact execCmd_store _ _
  · intro p hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hI.puts_good p hp
    · simp only [List.filterMap_cons, List.filterMap_nil] at hp
      cases hc : cmdPut (cmdOf inp) with
      | none => simp [hc] at hp
      | some p' =>
        simp only [hc, List.mem_singleton] at hp
        subst hp
        obtain ⟨k, v, rfl, rfl⟩ := cmdPut_cmdOf inp hinp _ hc
        exact goodVal_of_put k v hinp
  · intro y hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hI.done_ok y hy
    · exact ⟨_, hRx, hb⟩

/-- The initial facts: the invariant's, about the executed prefix `D`. -/
theorem execInv_init (Reg : GMap GoString RegEntry) (Res : GMap GoString (KOut))
    (D : List (List GoString)) (hReg : RegOk Reg)
    (h4 : ∀ x, (Res !! x).isSome ↔
        (∃ c j inp q tok, Reg !! x = some (.op c j inp q tok)) ∧ x ∈ (execLog (regB Reg) D).done)
    (h5 : ∀ x ∈ (execLog (regB Reg) D).done, ∃ e, Reg !! x = some e ∧ msg.batchFit (e.batch x))
    (h6 : ∀ x o, Res !! x = some o → ∃ c j inp q tok, Reg !! x = some (.op c j inp q tok) ∧
        (execLog (regB Reg) D).results x = some [ansOf inp o] ∧
        ∀ v, o = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil") :
    ExecInv Reg Res (execLog (regB Reg) D) := by
  refine ⟨h4, h6, execLog_storeOk _ _, ?_, h5⟩
  intro p hp
  obtain ⟨x, hx, b, hb, cmd, hc, hcp⟩ := execLog_putsFrom _ _ p hp
  obtain ⟨e, he, hok⟩ := h5 x hx
  simp only [regB, he, Option.map_some, Option.some.injEq] at hb
  subst hb
  cases e with
  | nil => simp [RegEntry.batch, nilBatch] at hc
  | sum =>
    simp only [RegEntry.batch, List.mem_singleton] at hc
    subst hc
    rw [hReg.2.2 _ he] at hcp; cases hcp
  | op c j inp q tok =>
    simp only [RegEntry.batch, List.mem_singleton] at hc
    subst hc
    have hinp := hReg.2.1 x c j inp q tok he
    obtain ⟨k, v, rfl, rfl⟩ := cmdPut_cmdOf _ hinp _ hcp
    exact goodVal_of_put k v hinp

/-- The mask of an update (`opAU`) inside the mask left by opening `smrN` or `consN`. -/
theorem raxos_mask (N : Namespace) (h : N = smrN ∨ N = consN) :
    ⊤ \ ↑raxosN ⊆ (⊤ \ ↑N : CoPset) := by
  intro p hp
  rw [LawfulSet.mem_diff] at hp ⊢
  refine ⟨hp.1, fun h' => hp.2 ?_⟩
  rcases h with rfl | rfl
  · exact ndisj_mem_ndot h'
  · exact ndisj_mem_ndot h'

/-! ## The ghost part -/

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

instance kit_decided_persistent (γ : QNames) (i : Int) (ids : List GoString) :
    Persistent (decided (GF := GF) γ i ids) := by
  unfold decided; infer_instance

/-- A registry entry's resource in `smrInv`, with the pending updates out of their later. -/
def regBodyN (γ : QNames) (Res : GMap GoString (KOut)) (x : GoString)
    (e : RegEntry) : IProp GF :=
  match e with
  | .nil => iprop(True)
  | .sum => iprop(True)
  | .op _ _ inp q tok =>
    iprop(∃ Φ : KOut → IProp GF,
      savedPredOwn q .discard Φ ∗
      match Res !! x with
      | none => opUpd γ inp Φ
      | some o => ▷ Φ o ∨ token tok)

/-- The resources of an execution under the open invariant. -/
def execRes (γ : QNames) (Reg : GMap GoString RegEntry) (Res : GMap GoString (KOut))
    (es : ExecSt) : IProp GF :=
  iprop(ghostVar γ.puts (1 : Qp).half es.puts.reverse ∗ ghostMapAuth γ.res 1 Res ∗
    ([∗map] x ↦ o ∈ Res, ghostMapElem γ.res x .discard o) ∗
    ([∗map] x ↦ e ∈ Reg, regBodyN γ Res x e))

theorem regBodyN_res (γ : QNames) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) (x : GoString) (o : KOut) :
    ([∗map] y ↦ e ∈ GMap.delete x Reg, regBodyN (GF := GF) γ Res y e) ⊢
      [∗map] y ↦ e ∈ GMap.delete x Reg, regBodyN γ (<[x := o]> Res) y e := by
  refine bigSepM_mono fun {y e} hy => ?_
  have hne : x ≠ y := by
    intro h; subst h
    have : (GMap.delete x Reg) !! x = none := GMap.lookup_delete _ _
    exact absurd hy (by simp [Iris.Std.PartialMap.get?] at *)
  unfold regBodyN
  rw [GMap.lookup_insert_ne _ _ hne]

/-- A registered request's update, one-shot or persistent, gives one to fire. -/
theorem opUpd_opAU (γ : QNames) (inp : KIn) (Φ : KOut → IProp GF) :
    opUpd γ inp Φ ⊢ opAU γ inp Φ := by
  unfold opUpd
  split
  · exact .rfl
  · exact intuitionistically_elim

/-- **A request's update fires** (from any mask holding `⊤ ∖ raxosN`, as paxos's `opAU_commit`),
at the abstract state `σ` of the puts `l`, the invariant's half of which is given: the puts `l'`
of the step's new state, and the caller's postcondition of the step's output. -/
theorem opAU_commit (γ : QNames) (M : CoPset) (hM : ⊤ \ ↑raxosN ⊆ M) (inp : KIn)
    (Φ : KOut → IProp GF) (σ : pure.Store) (l l' : List (GoString × GoString))
    (hσ : σ = kvAbs l) (hl' : kvAbs l' = (kvB.step inp σ).1) :
    ⊢ opAU γ inp Φ -∗ ghostVar γ.puts (1 : Qp).half l ={M}=∗
      ghostVar γ.puts (1 : Qp).half l' ∗ Φ (kvB.step inp σ).2 := by
  iintro HAU Hp
  unfold opAU
  imod fupd_mask_subseteq (PROP := IProp GF) hM with Hmask
  imod HAU with ⟨%σ0, Hown, Hcommit⟩
  iunfold ownState at Hown
  icases Hown with ⟨%l0, Hl, %hσ0⟩
  ihave %hl := ghostVar_agree $$ Hp Hl
  subst hl
  subst hσ0
  subst hσ
  imod ghostVar_update_halves l' $$ Hp Hl with ⟨Hp, Hl⟩
  imod Hcommit $$ [Hl] with HΦ
  · iunfold ownState
    iexists l'
    iframe Hl
    ipureintro; exact hl'.symm
  imod Hmask
  imodintro
  iframe Hp HΦ

theorem exec_one (γ : QNames) (E : CoPset) (hE : ⊤ \ ↑raxosN ⊆ E) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) (es : ExecSt) (x : GoString) (hReg : RegOk Reg)
    (hI : ExecInv Reg Res es) (hx : ∃ e, Reg !! x = some e ∧ msg.batchFit (e.batch x)) :
    ⊢@{IProp GF} execRes γ Reg Res es ={E}=∗ ∃ Res',
      ⌜ExecInv Reg Res' (execOne (regB Reg) es x)⌝ ∗ execRes γ Reg Res' (execOne (regB Reg) es x) := by
  by_cases hd : x ∈ es.done
  · rw [execOne_old _ es x hd]
    iintro H
    imodintro
    iexists Res
    iframe H
    ipureintro; exact hI
  obtain ⟨e, hRx, hb⟩ := hx
  cases e with
  | nil =>
    obtain ⟨hI', hputs⟩ := execInv_plain Reg Res es x _ hI hd hRx (by intros; simp)
      (by simp [RegEntry.batch, nilBatch]) hb
    iintro H
    imodintro
    iexists Res
    unfold execRes
    rw [hputs]
    iframe H
    ipureintro; exact hI'
  | sum =>
    obtain ⟨hI', hputs⟩ := execInv_plain Reg Res es x _ hI hd hRx (by intros; simp)
      (by simp [RegEntry.batch, hReg.2.2 x hRx]) hb
    iintro H
    imodintro
    iexists Res
    unfold execRes
    rw [hputs]
    iframe H
    ipureintro; exact hI'
  | op c j inp q tok =>
    have hinp := hReg.2.1 x c j inp q tok hRx
    have hnone : Res !! x = none := by
      cases h : Res !! x with
      | none => rfl
      | some o' => exact absurd ((hI.res_iff x).1 (by simp [h])).2 hd
    unfold execRes
    iintro ⟨Hp, Ha, Hm, Hb⟩
    ihave ⟨Hx, Hb⟩ := (bigSepM_delete (Φ := fun y e => regBodyN (GF := GF) γ Res y e)
      (i := x) hRx).1 $$ Hb
    iunfold regBodyN at Hx
    rw [hnone]
    icases Hx with ⟨%Φ, #Hsv, HU⟩
    ihave HAU := opUpd_opAU γ inp Φ $$ HU
    obtain ⟨_, hex⟩ := execCmd_step es.store inp hinp
    have hI' := execInv_op Reg Res es x c j inp q tok _ hI hd hRx hinp hb rfl
    have hσ1 : kvAbs (execOne (regB Reg) es x).puts.reverse = (kvB.step inp es.store).1 := by
      have h := hI'.store
      unfold storeOk at h
      rw [← h, execOne_op Reg es x c j inp q tok hd hRx, hex]
    imod opAU_commit γ E hE inp Φ es.store _ _ hI.store hσ1 $$ HAU Hp with ⟨Hp, HΦ⟩
    imod ghost_map_insert_persist x (kvB.step inp es.store).2 hnone $$ Ha with ⟨Ha, #Hel⟩
    imodintro
    iexists <[x := (kvB.step inp es.store).2]> Res
    iframe Hp Ha
    isplitr
    · ipureintro; exact hI'
    isplitl [Hm]
    · iapply (bigSepM_insert (Φ := fun y o => iprop(y ↪[γ.res]□ o)) (m := Res) (i := x) (x := (kvB.step inp es.store).2)
        hnone).2
      iframe Hel Hm
    iapply (bigSepM_delete (Φ := fun y e => regBodyN (GF := GF) γ (<[x := (kvB.step inp es.store).2]> Res) y e)
      (i := x) hRx).2
    isplitl [HΦ]
    · iunfold regBodyN
      rw [GMap.lookup_insert]
      iexists Φ
      iframe Hsv
      ileft
      inext
      iexact HΦ
    iapply regBodyN_res $$ Hb

theorem exec_ids (γ : QNames) (E : CoPset) (hE : ⊤ \ ↑raxosN ⊆ E) (Reg : GMap GoString RegEntry)
    (hReg : RegOk Reg) (xs : List GoString) :
    ∀ (Res : GMap GoString (KOut)) (es : ExecSt), ExecInv Reg Res es →
      (∀ x ∈ xs, ∃ e, Reg !! x = some e ∧ msg.batchFit (e.batch x)) →
      ⊢@{IProp GF} execRes γ Reg Res es ={E}=∗ ∃ Res',
        ⌜ExecInv Reg Res' (execIds (regB Reg) es xs)⌝ ∗
          execRes γ Reg Res' (execIds (regB Reg) es xs) := by
  induction xs with
  | nil =>
    intro Res es hI _
    rw [execIds_nil]
    iintro H
    imodintro
    iexists Res
    iframe H
    ipureintro; exact hI
  | cons x xs ih =>
    intro Res es hI hxs
    iintro H
    imod exec_one γ E hE Reg Res es x hReg hI (hxs x (by simp)) $$ H with ⟨%Res1, %hI1, H⟩
    rw [execIds_cons]
    iapply ih Res1 _ hI1 (fun y hy => hxs y (by simp [hy])) $$ H

/-- The registry's resources of `smrInv` give the ones without laters, under a later. -/
theorem regBody_later (γ : QNames) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) :
    ([∗map] x ↦ e ∈ Reg, match e with
      | .nil => iprop(True)
      | .sum => iprop(True)
      | .op _ _ inp q tok =>
        ∃ Φ : KOut → IProp GF,
          savedPredOwn q .discard Φ ∗
          match Res !! x with
          | none => ▷ opUpd γ inp Φ
          | some o => ▷ Φ o ∨ token tok) ⊢
      ▷ [∗map] x ↦ e ∈ Reg, regBodyN γ Res x e := by
  refine (bigSepM_mono fun {x e} _ => ?_).trans bigSepM_later.2
  cases e with
  | nil => unfold regBodyN; exact later_intro
  | sum => unfold regBodyN; exact later_intro
  | op c j inp q tok =>
    unfold regBodyN
    cases Res !! x with
    | none =>
      iintro ⟨%Φ, #Hs, HAU⟩
      inext
      iexists Φ
      iframe # ∗
    | some o =>
      dsimp only
      exact later_intro

/-- ... and back. -/
theorem regBody_unlater (γ : QNames) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) :
    ([∗map] x ↦ e ∈ Reg, regBodyN γ Res x e) ⊢
    ([∗map] x ↦ e ∈ Reg, match e with
      | .nil => iprop(True)
      | .sum => iprop(True)
      | .op _ _ inp q tok =>
        ∃ Φ : KOut → IProp GF,
          savedPredOwn q .discard Φ ∗
          match Res !! x with
          | none => ▷ opUpd γ inp Φ
          | some o => ▷ Φ o ∨ token tok) := by
  refine bigSepM_mono fun {x e} _ => ?_
  cases e with
  | nil => unfold regBodyN; exact .rfl
  | sum => unfold regBodyN; exact .rfl
  | op c j inp q tok =>
    unfold regBodyN
    cases Res !! x with
    | none =>
      iintro ⟨%Φ, #Hs, HAU⟩
      iexists Φ
      isplitr
      · iexact Hs
      inext
      iexact HAU
    | some o =>
      dsimp only
      exact .rfl

/-- The invariant's puts are the execution's, newest first. -/
theorem putsOf_eq (B : GoString → Option Batch) (D : List (List GoString)) :
    putsOf B D = (execLog B D).puts.reverse := rfl

/-- Registered batches are the registry's. -/
theorem regs_of_list (γ : QNames) (Reg : GMap GoString RegEntry) (B : GoString → Option Batch)
    (l : List GoString) :
    ⊢@{IProp GF} ghostMapAuth γ.reg 1 Reg -∗
      ([∗list] x ∈ l, ∃ b, ⌜B x = some b ∧ msg.batchFit b⌝ ∗ batchReg γ x b) -∗
      ⌜∀ x ∈ l, ∃ e, Reg !! x = some e ∧ B x = some (e.batch x) ∧ msg.batchFit (e.batch x)⌝ := by
  induction l with
  | nil => iintro _ _; ipureintro; simp
  | cons x l ih =>
    iintro Ha ⟨⟨%b, %hb, Hr⟩, Hl⟩
    iunfold batchReg at Hr
    icases Hr with ⟨%e, Hel, %hh⟩
    have he := hh.1
    ihave %hlk := ghost_map_lookup $$ Ha Hel
    ihave %hl := ih $$ Ha Hl
    ipureintro
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · subst he; exact ⟨e, hlk, hb.1, hb.2⟩
    · exact hl y hy

/-- A request's answer from the invariant's outputs. -/
theorem ans_of_res (γ : QNames) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) (x : GoString) (o : KOut) (c j : Nat)
    (inp : KIn) (q tok : GName)
    (hR : Reg !! x = some (.op c j inp q tok)) (hRes : Res !! x = some o)
    (hv : ∀ v, o = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil") :
    ⊢@{IProp GF} ([∗map] x ↦ e ∈ Reg, ghostMapElem γ.reg x .discard e) -∗
      ([∗map] x ↦ o ∈ Res, ghostMapElem γ.res x .discard o) -∗ opAns γ x (ansOf inp o) := by
  iintro Hre Hse
  ihave Hr := bigSepM_lookup (Φ := fun x e => iprop(ghostMapElem γ.reg x .discard e)) (i := x)
    hR $$ Hre
  ihave Hs := bigSepM_lookup (Φ := fun x o => iprop(ghostMapElem γ.res x .discard o)) (i := x)
    hRes $$ Hse
  unfold opAns opDone
  iexists c, j, inp, q, tok, o
  iframe Hr Hs
  ipureintro
  exact ⟨rfl, hv⟩

theorem kit_internal_eq_rewrite_wand {P Q : IProp GF} : ⊢ (P ≡ Q) -∗ Q -∗ P := by
  iintro #H HQ
  ihave #Hiff := internalEq_iff P Q $$ H
  icases Hiff with ⟨-, H2⟩
  iapply H2
  iexact HQ

/-- A registry entry's resource in `smrInv`, as written there. -/
def regBodyL (γ : QNames) (Res : GMap GoString (KOut)) (x : GoString)
    (e : RegEntry) : IProp GF :=
  match e with
  | .nil => iprop(True)
  | .sum => iprop(True)
  | .op _ _ inp q tok =>
    iprop(∃ Φ : KOut → IProp GF,
      savedPredOwn q .discard Φ ∗
      match Res !! x with
      | none => ▷ opUpd γ inp Φ
      | some o => ▷ Φ o ∨ token tok)

theorem regBodyL_of (γ : QNames) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) :
    ([∗map] x ↦ e ∈ Reg, match e with
      | .nil => iprop(True)
      | .sum => iprop(True)
      | .op _ _ inp q tok =>
        ∃ Φ : KOut → IProp GF,
          savedPredOwn q .discard Φ ∗
          match Res !! x with
          | none => ▷ opUpd γ inp Φ
          | some o => ▷ Φ o ∨ token tok) ⊢
      [∗map] x ↦ e ∈ Reg, regBodyL γ Res x e := .rfl

theorem regBodyL_to (γ : QNames) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) :
    ([∗map] x ↦ e ∈ Reg, regBodyL γ Res x e) ⊢
    ([∗map] x ↦ e ∈ Reg, match e with
      | .nil => iprop(True)
      | .sum => iprop(True)
      | .op _ _ inp q tok =>
        ∃ Φ : KOut → IProp GF,
          savedPredOwn q .discard Φ ∗
          match Res !! x with
          | none => ▷ opUpd γ inp Φ
          | some o => ▷ Φ o ∨ token tok) := .rfl

end iris

end Perennial.raxos
