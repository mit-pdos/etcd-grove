/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureP/Deps.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit P: the dependencies' range (H-X-3): every dependency entry (rows 0..2) of every copy, recovery
candidate and EPaxos message carrying deps is below `SLOTS` (`DInv`, an invariant of reachable
configurations). Sources: `updateAttributes` raises an entry only to an instance it then finds in
the box; `mergeAttributes` takes entries of two bounded deps; the no-op's and `startPhase1`'s
`deps[q] = i - 1` for `i` in the box; `nildeps`.
-/
module

public import Dsverify.Proof.gryff.PureA.Exec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureP

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.pureA

/-- Rows 0..2 of `D` below `SLOTS`. -/
def DB (D : Deps) : Prop := ∀ j : Nat, j < 3 → sint.Z (D.at j) < SLOTS

theorem DB_setAt {D : Deps} (h : DB D) (k : Nat) {x : w32} (hx : sint.Z x < SLOTS) :
    DB (D.setAt k x) := by
  intro j hj
  unfold Deps.setAt Deps.at
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  split
  · next he =>
    subst he
    split
    · simpa using hx
    · have := h k hj; unfold Deps.at at this; rw [List.getD_eq_getElem?_getD] at this
      simp_all
  · have := h j hj; unfold Deps.at at this; rw [List.getD_eq_getElem?_getD] at this; exact this

theorem updAttr_DB {s : RState} {cmds : List Cmd} {seq0 : w32} {deps0 : Deps} {rep : w32}
    {r : w32 × Deps × Bool} (h : updateAttributes s cmds seq0 deps0 rep = some r)
    (hd : DB deps0) : DB r.2.1 := by
  unfold updateAttributes at h
  opeel h
  rename_i w1 hx1 w2 hx2
  subst h
  show DB w1.2.1
  refine forIn_opt_invA _ _ _ (fun st : w32 × Deps × Bool => DB st.2.1) ?_ ?_ w1 hx1
  · exact hd
  intro q b st hb hf
  opeel hf
  · cases hf; exact hb
  · rename_i w3 hx3
    cases hf
    show DB w3.2.1
    refine forIn_opt_invA _ _ _ (fun st : w32 × Deps × Bool => DB st.2.1) ?_ ?_ w3 hx3
    · exact hb
    intro c b' st' hb' hf'
    opeel hf'
    all_goals (try (cases hf'; exact hb'))
    all_goals (
      cases hf'
      rename_i hin _
      apply DB_setAt hb'
      split at hin
      · next hbx => simp only [inBox, decide_eq_true_eq] at hbx; exact hbx.2.2.2
      · cases hin)

theorem forIn_id_mem {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (P : β → Prop) (h0 : P b) (hf : ∀ a ∈ l, ∀ b, P b → P (f a b).run.value) :
    P (forIn l b f).run := by
  induction l generalizing b with
  | nil => exact h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hf a List.mem_cons_self b h0
    cases hfa : f a b with
    | done b' => rw [hfa] at this; exact this
    | yield b' =>
      rw [hfa] at this
      exact ih b' this (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha'))

theorem merge_DB (s : RState) (seq1 : w32) {d1 : Deps} (seq2 : w32) {d2 : Deps} (h1 : DB d1)
    (h2 : DB d2) : DB (mergeAttributes s seq1 d1 seq2 d2).2.1 := by
  unfold mergeAttributes
  simp only []
  split <;> (try split) <;> simp only [Id.run_bind, Id.run_pure]
  all_goals (
    refine forIn_id_mem _ _ _ (fun x : Bool × Deps => DB x.2) ?_ ?_
    · exact h1
    intro q hq b hb
    have hq3 : q < 3 := by simp at hq; omega
    split
    · exact hb
    · split
      · split
        · exact DB_setAt hb q (h2 q hq3)
        · exact hb
      · exact hb)

/-! ## The invariant's parts -/

/-- A copy's deps and its recovery candidate's. -/
@[irreducible] def DC (c : Copy) : Prop :=
  DB c.deps ∧ ∀ lb, c.lb = some lb → ∀ ri, lb.recoveryInst = some ri → DB ri.deps

/-- A replica's copies. -/
@[irreducible] def DS (s : RState) : Prop := ∀ q i c, s.inst q i = some c → DC c

/-- A message's deps. -/
def MD : Msg → Prop
  | .preAccept m => DB m.deps
  | .preAcceptReply m => DB m.deps
  | .accept m => DB m.deps
  | .commit m => DB m.deps
  | .prepareReply m => DB m.deps
  | _ => True

def OD : Out → Prop
  | .send _ m => MD m
  | .ext _ => True

theorem DC.deps' {c : Copy} (h : DC c) : DB c.deps := by unfold DC at h; exact h.1
theorem DC.ri {c : Copy} (h : DC c) {lb : LB} (hl : c.lb = some lb) {ri : RecoveryInstance}
    (hr : lb.recoveryInst = some ri) : DB ri.deps := by unfold DC at h; exact h.2 lb hl ri hr
theorem DC.mk' {c : Copy} (h1 : DB c.deps)
    (h2 : ∀ lb, c.lb = some lb → ∀ ri, lb.recoveryInst = some ri → DB ri.deps) : DC c := by
  unfold DC; exact ⟨h1, h2⟩
theorem DS.dc {s : RState} (h : DS s) {q i : w32} {c : Copy} (hc : s.inst q i = some c) : DC c := by
  unfold DS at h; exact h q i c hc

theorem DB_nildeps : DB nildeps := by
  intro j hj; unfold nildeps Deps.at
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> decide
theorem DB_deps0 : DB [-1, -1, -1, 0, 0] := by
  intro j hj; unfold Deps.at
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> decide

theorem pred_lt {q i : w32} (h : ¬ (!inBox q i) = true) : sint.Z (i - 1) < SLOTS := by
  simp only [inBox, Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not] at h
  obtain ⟨-, -, h0, h1⟩ := h
  simp only [sint.Z, SLOTS] at *
  rw [BitVec.toInt_sub]
  have e1 : (1 : w32).toInt = 1 := by decide
  rw [e1, Int.bmod_def]; split <;> omega
theorem pred_lt' {q i : w32} (h : inBox q i = true) : sint.Z (i - 1) < SLOTS :=
  pred_lt (q := q) (by simp [h])

theorem sendTo_OD {q : w32} {m : Msg} {o : Out} (h : sendTo q m = some o) (hm : MD m) : OD o := by
  unfold sendTo at h
  cases hd : dstOf q with
  | none => rw [hd] at h; cases h
  | some d => rw [hd] at h; cases h; exact hm
theorem sendPeer_OD {s : RState} {q : w32} {m : Msg} {o : Out} (h : sendPeer s q m = some o)
    (hm : MD m) : OD o := by
  unfold sendPeer at h; split at h
  · cases h
  · exact sendTo_OD h hm
theorem bcast_OD {s : RState} {m : Msg} {os : List Out} (h : bcast s m = some os) (hm : MD m) :
    ∀ x ∈ os, OD x := by
  unfold bcast at h
  generalize peerOrder s = l at h
  induction l generalizing os with
  | nil => simp at h; subst h; simp
  | cons q l ih =>
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i o ho
      simp only [] at h
      split at h
      · cases h
      · rename_i os' hos
        cases h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact sendPeer_OD ho hm
        · exact ih hos x hx

/-! ## Combinators -/

theorem ds_inst {t t' : RState} (h : DS t) (e : t'.inst = t.inst) : DS t' := by
  unfold DS at *; intro q i c hc; rw [e] at hc; exact h q i c hc
theorem ds_setInst {t : RState} (h : DS t) {q i : w32} {c : Copy} (hc : DC c) :
    DS (t.setInst q i c) := by
  unfold DS at *; intro q' i' c' h'
  rw [setInst_inst] at h'
  split at h'
  · cases h'; exact hc
  · exact h q' i' c' h'
theorem ds_updConf {t : RState} (h : DS t) (cmds : List Cmd) (q i sq : w32) :
    DS (updateConflicts t cmds q i sq) := ds_inst h (updateConflicts_inst _ _ _ _ _).1
theorem ds_updCommitted {t t' : RState} {q : w32} (h : DS t) (hu : updateCommitted t q = some t') :
    DS t' := ds_inst h (updateCommitted_inst hu).1
theorem ds_proposeQ {t : RState} (h : DS t) (x : List Proposal) : DS { t with proposeQ := x } :=
  ds_inst h rfl
theorem ds_prevValTag {t : RState} (h : DS t) (x : Option ValTag) : DS { t with prevValTag := x } :=
  ds_inst h rfl
theorem ds_setCrt {t : RState} (h : DS t) (q x : w32) : DS (t.setCrt q x) := ds_inst h rfl
theorem ds_overwrite {t : RState} (h : DS t) (v : w64) (tg : model.Tag) : DS (t.overwrite v tg) :=
  ds_inst h (overwrite_frame t v tg).2.1

theorem od_nil : ∀ x ∈ ([] : List Out), OD x := by simp

theorem od_append {a b : List Out} (ha : ∀ x ∈ a, OD x) (hb : ∀ x ∈ b, OD x) : ∀ x ∈ a ++ b, OD x := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h
theorem od_single {o : Out} (h : OD o) : ∀ x ∈ [o], OD x := by
  intro x hx; rw [List.mem_singleton] at hx; subst hx; exact h

open Lean Elab Tactic Meta in
/-- `inst_try h => tac`: run `tac` with `h` bound to each hypothesis `_.inst _ _ = some _` (or
`updateAttributes _ _ _ _ _ = some _` for `attr_try`) until one closes the goal. -/
meta def tryHyps (head : Name) (k : Term → TacticM Unit) : TacticM Unit := withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOf head do continue
    let st ← saveState
    try
      let h ← Term.exprToSyntax d.toExpr
      k h
      if (← getUnsolvedGoals).isEmpty then return
      st.restore
    catch _ => st.restore
  throwError "tryHyps failed"

syntax "db_solve" : tactic
set_option hygiene false in
open Lean Elab Tactic Meta in
elab "db_inst" : tactic => tryHyps ``RState.inst fun h => do
  evalTactic (← `(tactic| with_reducible exact DC.deps' (DS.dc hs $h)))
set_option hygiene false in
open Lean Elab Tactic Meta in
elab "db_attr" : tactic => tryHyps ``updateAttributes fun h => do
  evalTactic (← `(tactic| with_reducible refine updAttr_DB $h ?_))
  evalTactic (← `(tactic| db_solve))
set_option hygiene false in
open Lean Elab Tactic Meta in
/-- `DB ri.deps` for a candidate some hypothesis names (`_.recoveryInst = some ri`), through the
copy holding it. -/
elab "dc_ri2" : tactic => tryHyps ``RState.inst fun h => do
  evalTactic (← `(tactic| exact DC.ri (DS.dc hs $h) (by assumption) (by assumption)))

set_option hygiene false in
open Lean Elab Tactic Meta in
/-- `DB ri.deps` for a candidate set in this step (`{.. recoveryInst := some x ..}.recoveryInst = some ri`). -/
elab "db_ri" : tactic => tryHyps ``LB.recoveryInst fun h => do
  evalTactic (← `(tactic| (have hh := $h; simp only [Option.some.injEq] at hh; subst hh; first
    | (simp only [riOf]; db_solve) | db_solve)))

set_option hygiene false in
macro_rules
  | `(tactic| db_solve) => `(tactic| first
      | with_reducible exact hm
      | with_reducible exact DB_nildeps
      | with_reducible exact DB_deps0
      | db_inst
      | db_attr
      | (with_reducible refine merge_DB _ _ _ ?_ ?_
         all_goals db_solve)
      | (with_reducible refine DB_setAt ?_ _ ?_
         · db_solve
         · first | exact pred_lt ‹_› | exact pred_lt' ‹_›))

set_option hygiene false in
open Lean Elab Tactic Meta in
elab "dc_ri" : tactic => tryHyps ``RState.inst fun h => do
  evalTactic (← `(tactic| exact DC.ri (DS.dc hs $h) (by assumption) (by assumption)))

theorem od_ext (x : Ext) : ∀ y ∈ [(kahn.Out.ext x : Out)], OD y := by
  intro y hy; rw [List.mem_singleton] at hy; subst hy; trivial

theorem mapM_OD {l : List w32} {f : w32 → Option Out} {os : List Out}
    (hf : ∀ q o, f q = some o → OD o) (h : l.mapM f = some os) : ∀ x ∈ os, OD x := by
  induction l generalizing os with
  | nil => simp at h; subst h; simp
  | cons q l ih =>
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i o ho
      simp only [] at h
      split at h
      · cases h
      · rename_i os' hos
        cases h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hf q _ ho
        · exact ih hos x hx

theorem mapM_sendTo_OD {l : List w32} {f : w32 → Option Out} {os : List Out}
    (h : l.mapM f = some os) (hf : ∀ q o, f q = some o → OD o) : ∀ x ∈ os, OD x := mapM_OD hf h

theorem mapM_sendTo_OD' {l : List w32} {m : Msg} {os : List Out}
    (h : l.mapM (fun q => sendTo q m) = some os) (hm : MD m) : ∀ x ∈ os, OD x :=
  mapM_OD (fun _ _ hq => sendTo_OD hq hm) h

theorem mapM_sendPeer_OD' {l : List w32} {s : RState} {m : Msg} {os : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some os) (hm : MD m) : ∀ x ∈ os, OD x :=
  mapM_OD (fun _ _ hq => sendPeer_OD hq hm) h

theorem shortCircuit_OD {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : ∀ x ∈ o, OD x := by
  unfold shortCircuit at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_invA _ _ _ (fun p : RState × List Out => ∀ x ∈ p.2, OD x) ?_ ?_ _ ‹_›
    · simp
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; first | exact hb | exact od_append hb (od_ext _))

theorem shortCircuit_ite_OD {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : ∀ x ∈ o, OD x := by
  split at h
  · exact shortCircuit_OD h
  · cases h; exact od_nil
open Lean Elab Tactic Meta in
/-- An output from a send (`sendTo`, `sendPeer`) or a broadcast among the hypotheses. -/
elab "od_one" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    let fn := lhs.getAppFn
    unless fn.isConst do continue
    let n := fn.constName!
    let bc : List Name := [``bcastPreAccept, ``bcastAccept, ``bcastCommit, ``bcastPrepare, ``bcast]
    let lem : Ident :=
      if n = ``sendTo then mkIdent ``sendTo_OD
      else if n = ``sendPeer then mkIdent ``sendPeer_OD
      else if n = ``List.mapM then mkIdent ``mapM_sendTo_OD
      else mkIdent ``bcast_OD
    unless ([``sendTo, ``sendPeer, ``List.mapM] ++ bc).contains n do continue
    let st ← saveState
    try
      let h ← Term.exprToSyntax d.toExpr
      if n = ``List.mapM then
        evalTactic (← `(tactic| first | exact mapM_sendTo_OD' $h trivial | exact mapM_sendPeer_OD' $h trivial))
      else
        evalTactic (← `(tactic| (exact $lem $h (by first | trivial | (simp only [MD]; done) | (simp only [MD]; db_solve) | (simp only [MD]; dc_ri2)); done)))
      return
    catch _ => st.restore
  throwError "od_one failed"

open Lean Elab Tactic Meta in
meta def odSc1 : TacticM Unit := tryHyps ``shortCircuit fun h => do
  evalTactic (← `(tactic| exact shortCircuit_OD $h))

open Lean Elab Tactic Meta in
meta def odSc2 : TacticM Unit := tryHyps ``ite fun h => do
  evalTactic (← `(tactic| exact shortCircuit_ite_OD $h))

open Lean Elab Tactic Meta in
elab "od_sc" : tactic => odSc1 <|> odSc2

macro "od_part" : tactic => `(tactic| (
  first
    | exact od_nil
    | exact od_ext _
    | (apply od_single; od_one)
    | od_one
    | od_sc))

macro "od_solve" : tactic => `(tactic| (
  first
    | exact od_nil
    | exact od_ext _
    | (apply od_single; od_one)
    | od_one
    | (apply od_append <;> first | exact od_nil | exact od_ext _ | (apply od_single; od_one) | od_one)))

macro "g_solve" : tactic => `(tactic| (
  first
    | od_part
    | (apply od_append
       · od_part
       · od_part)))

macro "dc_solve" : tactic => `(tactic| (
  refine DC.mk' ?_ ?_
  · first | db_solve | (simp only []; db_solve) | (simp only [riOf]; db_solve) | dc_ri2 | db_ri
  · intro lb hlb ri hri
    first
      | (cases hlb; done)
      | dc_ri
      | (simp only [Option.some.injEq] at hlb; subst hlb; simp only [] at hri
         first
           | (cases hri; done)
           | dc_ri
           | (simp only [Option.some.injEq] at hri; subst hri; simp only []; db_solve)
           | (simp only [Option.some.injEq] at hri; subst hri; simp only [riOf]; db_solve)
           | (simp only [Option.some.injEq] at hri; subst hri; simp only []; dc_ri2)
           | db_solve)))

open Lean Elab Tactic Meta in
/-- Take apart a goal `DS e` along `e`'s construction (leaving the new copies' `DC` goals). -/
meta partial def dsSplit : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  unless tgt.isAppOfArity ``DS 1 do return
  let e := tgt.appArg!
  let run (t : TSyntax `tactic) : TacticM Unit := do
    evalTactic t
  if e.isFVar then
    -- the replica's state, or an `updateCommitted` result
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, lhs, rhs) := ty.eq? then
        if lhs.isAppOf ``updateCommitted && rhs.isAppOfArity ``Option.some 2 && rhs.appArg! == e then
          let h ← Term.exprToSyntax d.toExpr
          run (← `(tactic| refine ds_updCommitted ?_ $h))
          dsSplit
          return
    run (← `(tactic| assumption))
    return
  let fn := e.getAppFn
  unless fn.isConst do throwError "dsSplit: {e}"
  let n := fn.constName!
  if n == ``RState.setInst then
    run (← `(tactic| refine ds_setInst ?_ ?_))
    dsSplit
  else if n == ``updateConflicts then
    run (← `(tactic| refine ds_updConf ?_ _ _ _ _))
    dsSplit
  else if n == ``RState.setCrt then
    run (← `(tactic| refine ds_setCrt ?_ _ _))
    dsSplit
  else if n == ``RState.overwrite then
    run (← `(tactic| refine ds_overwrite ?_ _ _))
    dsSplit
  else if n == ``RState.mk then
    -- a record update: its `inst` field is some state's
    let args := e.getAppArgs
    let instF := args[8]!
    unless instF.isAppOfArity ``RState.inst 1 do throwError "dsSplit: inst field {instF}"
    let t ← Term.exprToSyntax instF.appArg!
    run (← `(tactic| refine ds_inst (t := $t) ?_ rfl))
    dsSplit
  else throwError "dsSplit: {n}"

open Lean Elab Tactic Meta in
elab "ds_split" : tactic => dsSplit

macro "ds_fin" : tactic => `(tactic| (
  ds_split
  all_goals dc_solve))

macro "d_fin" : tactic => `(tactic| (
  refine ⟨?_, ?_⟩
  · ds_fin
  · od_solve))

set_option maxRecDepth 20000

theorem stepCommit_D {s s' : RState} {m : ECommitM} {o : List Out} (hs : DS s) (hm : DB m.deps)
    (h : stepCommit s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  unfold stepCommit at h; peel h
  all_goals (cases h; d_fin)

theorem stepAccept_D {s s' : RState} {m : EAcceptM} {o : List Out} (hs : DS s) (hm : DB m.deps)
    (h : stepAccept s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  unfold stepAccept at h; peel h
  all_goals (cases h; d_fin)

theorem leaderCommit_D {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out} (hs : DS s)
    (hc : DB c.deps) (hl : ∀ ri, lb.recoveryInst = some ri → DB ri.deps)
    (h : leaderCommit s q i c lb = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  have hm := hc
  have hdc : DC { c with status := St.COMMITTED, lb := some lb } := by
    refine DC.mk' hc ?_
    intro lb' hlb ri hri; cases hlb; exact hl ri hri
  have hdc' : DC { c with status := St.COMMITTED, lb := none } := by
    refine DC.mk' hc ?_
    intro lb' hlb; cases hlb
  unfold leaderCommit at h; peel h
  all_goals (
    cases h
    refine ⟨?_, ?_⟩
    · ds_split
      all_goals first | exact hdc | exact hdc'
    · od_solve)

theorem startPhase1_D {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (hs : DS s) (h : startPhase1 s q i b ps cs = .ok (s', o)) :
    DS s' ∧ ∀ x ∈ o, OD x := by
  have hm : DB [-1, -1, -1, 0, 0] := DB_deps0
  unfold startPhase1 at h; peel h
  all_goals (cases h; d_fin)

macro "d_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; d_fin; done)
    | (refine leaderCommit_D ?_ ?_ ?_ $h:ident
       · ds_split
         all_goals dc_solve
       · first | db_solve | (simp only []; db_solve)
       · intro ri hri
         first
           | dc_ri
           | (simp only [] at hri; first | dc_ri | (cases hri; done)))
    | (refine startPhase1_D ?_ $h:ident
       ds_split
       all_goals dc_solve)
    | skip)))

theorem stepPreAccept_D {s s' : RState} {m : PreAcceptM} {o : List Out} (hs : DS s)
    (hm : DB m.deps) (h : stepPreAccept s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  unfold stepPreAccept at h; d_close h
theorem stepPreAcceptReply_D {s s' : RState} {m : PreAcceptReplyM} {o : List Out} (hs : DS s)
    (hm : DB m.deps) (h : stepPreAcceptReply s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  unfold stepPreAcceptReply at h; d_close h
theorem stepPreAcceptOK_D {s s' : RState} {m : PreAcceptOKM} {o : List Out} (hs : DS s)
    (h : stepPreAcceptOK s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  have hm := DB_nildeps
  unfold stepPreAcceptOK at h; d_close h
theorem stepAcceptReply_D {s s' : RState} {m : AcceptReplyM} {o : List Out} (hs : DS s)
    (h : stepAcceptReply s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  have hm := DB_nildeps
  unfold stepAcceptReply at h; d_close h
theorem stepPrepare_D {s s' : RState} {m : PrepareM} {o : List Out} (hs : DS s)
    (h : stepPrepare s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  have hm := DB_nildeps
  unfold stepPrepare at h; peel h
  all_goals (cases h)
  · d_fin
  all_goals (rename_i hb; simp only [hb, ite_true, ite_false, Bool.false_eq_true] at *; d_fin)

set_option maxHeartbeats 2000000 in
theorem stepPrepareReply_D {s s' : RState} {m : PrepareReplyM} {o : List Out} (hs : DS s)
    (hm : DB m.deps) (h : stepPrepareReply s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  unfold stepPrepareReply at h; peel h
  all_goals (first
    | (cases h; d_fin; done)
    | (refine startPhase1_D ?_ h
       ds_split
       all_goals dc_solve))
theorem handleExecuted_D {s s' : RState} {m : ExecutedM} {o : List Out} (hs : DS s)
    (h : handleExecuted s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  have hm := DB_nildeps
  unfold handleExecuted at h; d_close h
theorem stepRecover_D {s s' : RState} {q i : w32} {o : List Out} (hs : DS s)
    (h : stepRecover s q i = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  have hm := DB_nildeps
  unfold stepRecover at h; d_close h
theorem stepExec_D {s s' : RState} {q i : w32} {o : List Out} (hs : DS s)
    (h : stepExec s q i = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  have hm := DB_nildeps
  unfold stepExec at h; d_close h

/-! ## The Gryff handlers: copies untouched, no EPaxos message -/

macro "g_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (cases $h:ident; g_solve)))

theorem stepRead1_OD {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepRead1 at h; g_close h
theorem stepRead2_OD {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepRead2 at h; g_close h
theorem stepWrite1_OD {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepWrite1 at h; g_close h
theorem stepWrite2_OD {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepWrite2 at h; g_close h
theorem stepRead1Reply_OD {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepRead1Reply at h; g_close h
theorem stepRead2Reply_OD {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepRead2Reply at h; g_close h
theorem stepWrite1Reply_OD {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepWrite1Reply at h; g_close h
theorem stepWrite2Reply_OD {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepWrite2Reply at h; g_close h
theorem stepClientWrite_OD {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepClientWrite at h; g_close h
theorem stepClientRead_OD {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : ∀ x ∈ o, OD x := by
  unfold stepClientRead at h; g_close h

theorem frame_D {s s' : RState} {o : List Out} (hs : DS s) (hf : Frame s s') (ho : ∀ x ∈ o, OD x) :
    DS s' ∧ ∀ x ∈ o, OD x := ⟨ds_inst hs hf.2.1, ho⟩

theorem handlePropose_D {s s' : RState} {p : Proposal} {o : List Out} (hs : DS s)
    (h : handlePropose s p = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  obtain ⟨-, -, h⟩ := handlePropose_ok h
  unfold handleProposeBody at h
  exact startPhase1_D (ds_proposeQ (ds_setCrt hs _ _) _) h

theorem stepClientRMW_D {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (hs : DS s) (h : stepClientRMW s rid cid k d a b = .ok (s', o)) :
    DS s' ∧ ∀ x ∈ o, OD x := by
  unfold stepClientRMW at h; peel h
  exact handlePropose_D (ds_inst (t' := { s with nReqs := s.nReqs + 1, used := (cid, rid) :: s.used })
    hs rfl) h

theorem stepExecuteOverwrite_D {s s' : RState} {m : ExecuteOverwriteM} {o : List Out} (hs : DS s)
    (h : stepExecuteOverwrite s m = .ok (s', o)) : DS s' ∧ ∀ x ∈ o, OD x := by
  have hs' : DS (s.overwrite m.v m.t) := ds_overwrite hs _ _
  unfold stepExecuteOverwrite at h; peel h
  · exact handleExecuted_D hs' h
  · cases h; exact ⟨hs', by od_solve⟩

/-- **Every step** keeps the copies' deps in range and sends messages with deps in range. -/
theorem step_D {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out} (hs : DS s)
    (hm : ∀ m, e.recv = some m → MD m) (h : stepR r s e = .ok (s', o)) :
    DS s' ∧ ∀ x ∈ o, OD x := by
  cases e with
  | read => exact frame_D hs (stepClientRead_frame h) (stepClientRead_OD h)
  | write => exact frame_D hs (stepClientWrite_frame h) (stepClientWrite_OD h)
  | rmw => exact stepClientRMW_D hs h
  | forceWrite => cases h; exact ⟨hs, od_nil⟩
  | recover => exact stepRecover_D hs h
  | exec => exact stepExec_D hs h
  | msg m =>
    have hmd := hm m rfl
    cases m with
    | read1 => exact frame_D hs (stepRead1_frame h) (stepRead1_OD h)
    | read2 => exact frame_D hs (stepRead2_frame h) (stepRead2_OD h)
    | write1 => exact frame_D hs (stepWrite1_frame h) (stepWrite1_OD h)
    | write2 => exact frame_D hs (stepWrite2_frame h) (stepWrite2_OD h)
    | read1Reply => exact frame_D hs (stepRead1Reply_frame h) (stepRead1Reply_OD h)
    | read2Reply => exact frame_D hs (stepRead2Reply_frame h) (stepRead2Reply_OD h)
    | write1Reply => exact frame_D hs (stepWrite1Reply_frame h) (stepWrite1Reply_OD h)
    | write2Reply => exact frame_D hs (stepWrite2Reply_frame h) (stepWrite2Reply_OD h)
    | prepare => exact stepPrepare_D hs h
    | preAccept => exact stepPreAccept_D hs hmd h
    | accept => exact stepAccept_D hs hmd h
    | commit => exact stepCommit_D hs hmd h
    | prepareReply => exact stepPrepareReply_D hs hmd h
    | preAcceptReply => exact stepPreAcceptReply_D hs hmd h
    | preAcceptOK => exact stepPreAcceptOK_D hs h
    | acceptReply => exact stepAcceptReply_D hs h
    | executed => exact handleExecuted_D hs h
    | executeOverwrite => exact stepExecuteOverwrite_D hs h

/-! ## Over runs -/

/-- The invariant of a configuration. -/
def DInv (c : kahn.Cfg gNet) : Prop :=
  (∀ r, DS (c.st r)) ∧ ∀ r m, m ∈ c.inflight r → MD m

theorem dinv_init : DInv (kahn.Cfg.init gNet) := by
  refine ⟨fun r => ?_, fun r m h => by simp [kahn.Cfg.init] at h⟩
  unfold DS; intro q i c h; simp [kahn.Cfg.init, gNet, RState.init] at h

theorem sentTo_mem' {j : Fin 3} {o : List Out} {m : Msg} (h : m ∈ kahn.sentTo gNet j o) :
    kahn.Out.send j m ∈ o := by
  simp only [kahn.sentTo] at h
  obtain ⟨x, hx, hm⟩ := List.mem_filterMap.1 h
  match x with
  | .send d m' =>
    by_cases hd : d = j
    · subst hd; simp at hm; cases hm; exact hx
    · simp [hd] at hm
  | .ext _ => simp at hm

theorem dinv_step {c c' : kahn.Cfg gNet} {r : Fin 3} {e : Ev} {x : List Ext} (hI : DInv c)
    (hs : kahn.GStep c r e c' x) : DInv c' := by
  obtain ⟨s', o, hst, hrecv, _, hc1, hc2⟩ := hs
  have hst' : stepR r (c.st r) e = .ok (s', o) := gstep_ok hst
  obtain ⟨hS, hO⟩ := step_D (hI.1 r) (fun m hm => hI.2 r m (hrecv m hm)) hst'
  refine ⟨fun j => ?_, fun j m hm => ?_⟩
  · rw [hc1]; simp only []
    split
    · exact hS
    · exact hI.1 j
  · rw [hc2] at hm
    simp only at hm
    rcases List.mem_append.1 hm with hm | hm
    · have hold : m ∈ c.inflight j := by
        split at hm
        · cases hrc : gNet.recv e with
          | none => rw [hrc] at hm; exact hm
          | some m0 => rw [hrc] at hm; exact List.mem_of_mem_erase hm
        · exact hm
      exact hI.2 j m hold
    · exact hO _ (sentTo_mem' hm)

theorem dinv_run {c c' : kahn.Cfg gNet} {l : List Label} (h : kahn.GRun c l c') (hI : DInv c) :
    DInv c' := by
  induction h with
  | nil => exact hI
  | cons hs _ ih => exact ih (dinv_step hI hs)

/-- **The deps bound** in a reachable configuration. -/
theorem deps_reach {l : List Label} {c : kahn.Cfg gNet} (h : kahn.GRun (kahn.Cfg.init gNet) l c)
    (r : Fin 3) {q i : w32} {cp : Copy} (hc : (c.st r).inst q i = some cp) :
    ∀ j : Nat, j < 3 → sint.Z (cp.deps.at j) < SLOTS :=
  DC.deps' (DS.dc ((dinv_run h dinv_init).1 r) hc)

end Perennial.gryff.pureP
