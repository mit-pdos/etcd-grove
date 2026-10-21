/-
`confchange.Restore` as a model (2026-10-14, reconfiguration stage B8), Lean-first: the
changes it replays a `ConfState` as, and the configuration they produce.

`Restore(chg, cs)` (confchange/restore.go) turns `cs` into single changes
(`toConfChangeSingle`) and runs them on the empty tracker:

* not joint (`VotersOutgoing` empty): one `Simple` per change of `in` -- `AddNode` per voter,
  `AddLearnerNode` per learner, then per staged learner (`restoreInCC [] ...`);
* joint: one `Simple(AddNode id)` per outgoing voter (`restoreOutCC`), which builds the outgoing
  configuration as a simple one, then **one** `EnterJoint(cs.AutoLeave, in...)` with
  `in` = `RemoveNode` per outgoing voter, `AddNode` per voter, `AddLearnerNode` per learner and
  per staged learner (`restoreInCC`).

`restoreM` is that, on the model of `InvConfchange.lean` (`simpleM`, `enterJointM`: the same
functions `ccApplyM` is made of); `none` when a step errs. `restoreM_wf`: on a well-formed
`ConfState` (`CSWf`, what `checkInvariants` accepts of the configuration it denotes, plus no
`0` id and at least one voter) it answers the configuration the `ConfState` denotes
(`csCfgM`, as `cfgStateC`). `AutoLeave` is dropped when the state is not joint (only the
joint path passes it to `EnterJoint`); `csCfgM` says so.
-/
module

public import Proof.go_etcd_io.raft.v3.CCApplyC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section model
variable [FfiSyntax]

/-- `pb.ConfChangeSingle{Type: pb.ConfChangeRemoveNode, NodeId: id}`. -/
abbrev removeNodeCC (id : w64) : ConfChangeSingleM :=
  { Type' := W32 1, NodeId' := id }

/-- `toConfChangeSingle`'s `out`: one `AddNode` per outgoing voter. -/
def restoreOutCC (vo : List w64) : List ConfChangeSingleM := vo.map addNodeCC

/-- `toConfChangeSingle`'s `in`: one `RemoveNode` per outgoing voter, then one `AddNode` per
voter, one `AddLearnerNode` per learner, one `AddLearnerNode` per staged learner. -/
def restoreInCC (vo v l ln : List w64) : List ConfChangeSingleM :=
  vo.map removeNodeCC ++ v.map addNodeCC ++ l.map addLearnerCC ++ ln.map addLearnerCC

/-- One `Simple([c])` per change, in order (`Restore`'s ops chained by `chain`). -/
def simpleFold : List ConfChangeSingleM → CCState → Option CCState
  | [], s => some s
  | c :: cs, s => (simpleM [c] s).bind (simpleFold cs)

/-- The changes `Restore` runs as `Simple` ops: the incoming ones when not joint, the
outgoing ones when joint. -/
def restoreSimpleOps (vo v l ln : List w64) : List ConfChangeSingleM :=
  if vo = [] then restoreInCC [] v l ln else restoreOutCC vo

/-- `Restore(chg, cs)` on the empty tracker (`cfgState ∅ ∅`), for a `ConfState` with
`VotersOutgoing = vo`, `Voters = v`, `Learners = l`, `LearnersNext = ln`, `AutoLeave = al`. -/
def restoreM (vo v l ln : List w64) (al : Bool) : Option CCState :=
  if vo = [] then simpleFold (restoreSimpleOps vo v l ln) (cfgState ∅ ∅)
  else (simpleFold (restoreSimpleOps vo v l ln) (cfgState ∅ ∅)).bind
    (enterJointM al (restoreInCC vo v l ln))

/-- The configuration a `ConfState`'s lists denote; `AutoLeave` only when joint (what
`Restore` keeps of it). -/
def csCfgM (vo v l ln : List w64) (al : Bool) : CfgM :=
  { incoming := GMap.listToSet v, outgoing := GMap.listToSet vo,
    learners := GMap.listToSet l, learnersNext := GMap.listToSet ln,
    autoLeave := if vo = [] then false else al }

/-- A well-formed `ConfState`: at least one voter, no `0` id (which `Changer.apply` skips),
a learner neither an incoming nor an outgoing voter, a staged learner an outgoing voter that
is neither an incoming voter nor a learner, no staged learner when not joint. These are
`checkInvariants`' conditions on the configuration it denotes (`csCfgM_cfgInv`), with "a staged
learner is no incoming voter", which every reachable configuration has (`CCGood`-like:
`makeLearner` removes the id from the incoming voters before staging it, `makeVoter` unstages
it). Duplicates are allowed (`Restore` is idempotent on them). -/
def CSWf (vo v l ln : List w64) : Prop :=
  v ≠ [] ∧
  (∀ x, x ∈ vo ∨ x ∈ v ∨ x ∈ l ∨ x ∈ ln → x ≠ W64 0) ∧
  (∀ x, x ∈ l → x ∉ v ∧ x ∉ vo) ∧
  (∀ x, x ∈ ln → x ∈ vo ∧ x ∉ v ∧ x ∉ l) ∧
  (vo = [] → ln = [])

theorem simpleFold_append (l1 l2 : List ConfChangeSingleM) (s : CCState) :
    simpleFold (l1 ++ l2) s = (simpleFold l1 s).bind (simpleFold l2) := by
  induction l1 generalizing s with
  | nil => simp [simpleFold]
  | cons y l ih =>
    simp only [List.cons_append, simpleFold]
    cases simpleM [y] s with
    | none => rfl
    | some s' => simp [ih]

/-- A prefix of a fold that succeeds succeeds, and the next step from it too. -/
theorem simpleFold_step (l : List ConfChangeSingleM) (s s' : CCState) (j : Nat)
    (c : ConfChangeSingleM) (Hc : l[j]? = some c) (H : simpleFold l s = some s') :
    ∃ sj sj1, simpleFold (l.take j) s = some sj ∧ simpleM [c] sj = some sj1 ∧
      simpleFold (l.take (j + 1)) s = some sj1 := by
  obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.1 Hc
  have hl : l = l.take j ++ [c] ++ l.drop (j + 1) := by
    rw [List.append_assoc, List.singleton_append, ← hcj, ← List.drop_eq_getElem_cons hj,
      List.take_append_drop]
  have ht : l.take (j + 1) = l.take j ++ [c] := by
    rw [List.take_add_one, Hc]; rfl
  rw [hl, simpleFold_append, simpleFold_append] at H
  cases h1 : simpleFold (l.take j) s with
  | none => rw [h1] at H; cases H
  | some sj =>
    rw [h1] at H
    simp only [Option.bind_some, simpleFold] at H
    cases h2 : simpleM [c] sj with
    | none => rw [h2] at H; cases H
    | some sj1 =>
      refine ⟨sj, sj1, rfl, h2, ?_⟩
      rw [ht, simpleFold_append, h1]
      simp [simpleFold, h2]

/-! ### The simple path -/

theorem simpleFold_addNodes (v : List w64) (V L : GSet w64)
    (H0 : ∀ x, x ∈ v → x ≠ W64 0 ∧ x ∉ L) (Hd : ∀ k, k ∈ L → k ∉ V) :
    ∃ V', (∀ k, k ∈ V' ↔ k ∈ V ∨ k ∈ v) ∧ (∀ k, k ∈ L → k ∉ V') ∧
      simpleFold (v.map addNodeCC) (cfgState V L) = some (cfgState V' L) := by
  induction v generalizing V with
  | nil => exact ⟨V, fun k => by simp, Hd, rfl⟩
  | cons x xs ih =>
    obtain ⟨hx0, hxL⟩ := H0 x (by simp)
    have Hd' : ∀ k, k ∈ L → k ∉ (<[x := ()]> V : GSet w64) := by
      intro k hk h
      rcases (gset_mem_insert V x k).1 h with h | h
      · subst h; exact hxL hk
      · exact Hd k hk h
    obtain ⟨V', HV', HdV', Hf⟩ := ih (<[x := ()]> V)
      (fun y hy => H0 y (List.mem_cons_of_mem _ hy)) Hd'
    refine ⟨V', fun k => ?_, HdV', ?_⟩
    · rw [HV', gset_mem_insert, List.mem_cons]; simp only [or_assoc, or_comm]
    · simp only [List.map_cons, simpleFold]
      rw [simpleM_cfgState_addNode V L x hx0 hxL Hd]
      exact Hf

theorem simpleFold_addLearners (l : List w64) (V L : GSet w64) (hne : V ≠ ∅)
    (H0 : ∀ x, x ∈ l → x ≠ W64 0 ∧ x ∉ V) (Hd : ∀ k, k ∈ L → k ∉ V) :
    ∃ L', (∀ k, k ∈ L' ↔ k ∈ L ∨ k ∈ l) ∧ (∀ k, k ∈ L' → k ∉ V) ∧
      simpleFold (l.map addLearnerCC) (cfgState V L) = some (cfgState V L') := by
  induction l generalizing L with
  | nil => exact ⟨L, fun k => by simp, Hd, rfl⟩
  | cons x xs ih =>
    obtain ⟨hx0, hxV⟩ := H0 x (by simp)
    have Hd' : ∀ k, k ∈ (<[x := ()]> L : GSet w64) → k ∉ V := by
      intro k h
      rcases (gset_mem_insert L x k).1 h with h | h
      · subst h; exact hxV
      · exact Hd k h
    obtain ⟨L', HL', HdL', Hf⟩ := ih (<[x := ()]> L)
      (fun y hy => H0 y (List.mem_cons_of_mem _ hy)) Hd'
    refine ⟨L', fun k => ?_, HdL', ?_⟩
    · rw [HL', gset_mem_insert, List.mem_cons]; simp only [or_assoc, or_comm]
    · simp only [List.map_cons, simpleFold]
      rw [simpleM_cfgState_addLearner V L x hx0 hxV hne Hd]
      exact Hf

theorem gset_ne_empty_of_mem {X : GSet w64} {x : w64} (h : x ∈ X) : X ≠ ∅ := by
  intro e; rw [e] at h; exact GMap.not_elem_of_empty _ h

/-- The simple path from `cfgState V L`: the voters, then the learners. -/
theorem simpleFold_restoreIn (v l : List w64) (hv : v ≠ [])
    (H0 : ∀ x, x ∈ v ∨ x ∈ l → x ≠ W64 0) (Hl : ∀ x, x ∈ l → x ∉ v) :
    simpleFold (restoreInCC [] v l []) (cfgState ∅ ∅) =
      some (cfgState (GMap.listToSet v) (GMap.listToSet l)) := by
  obtain ⟨V', HV', -, Hf1⟩ := simpleFold_addNodes v ∅ ∅
    (fun x hx => ⟨H0 x (.inl hx), GMap.not_elem_of_empty _⟩)
    (fun k hk => absurd hk (GMap.not_elem_of_empty _))
  have eV : V' = GMap.listToSet v := GMap.set_eq fun k => by
    rw [HV', GMap.elem_of_list_to_set]
    exact ⟨fun h => h.elim (fun h' => absurd h' (GMap.not_elem_of_empty _)) id, .inr⟩
  subst eV
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil v hv
  obtain ⟨L', HL', -, Hf2⟩ := simpleFold_addLearners l (GMap.listToSet v) ∅
    (gset_ne_empty_of_mem ((GMap.elem_of_list_to_set _ _).2 hx0))
    (fun x hx => ⟨H0 x (.inr hx), by rw [GMap.elem_of_list_to_set]; exact Hl x hx⟩)
    (fun k hk => absurd hk (GMap.not_elem_of_empty _))
  have eL : L' = GMap.listToSet l := GMap.set_eq fun k => by
    rw [HL', GMap.elem_of_list_to_set]
    exact ⟨fun h => h.elim (fun h' => absurd h' (GMap.not_elem_of_empty _)) id, .inr⟩
  subst eL
  simp only [restoreInCC, List.map_nil, List.nil_append, List.append_nil]
  rw [simpleFold_append, Hf1]
  exact Hf2

/-! ### The joint path: `EnterJoint`'s changes -/

/-- A joint state inside `EnterJoint` (`AutoLeave` off until `checkAndReturn`): incoming `I`,
outgoing `O`, learners `L`, staged learners `N` (within `O`), each voter of either half a
non-learner. -/
def jst (I O L N : GSet w64) : CCState :=
  { cfg := { incoming := I, outgoing := O, learners := L, learnersNext := N, autoLeave := false },
    prs := cfgFlags (I ∪ O) L }

theorem applyOne_remove (I O : GSet w64) (x : w64) (hx : x ≠ W64 0) (hO : x ∈ O) :
    applyOne (removeNodeCC x) (jst I O ∅ ∅) = some (jst (GMap.delete x I) O ∅ ∅) := by
  have hx' : (removeNodeCC x).NodeId' ≠ W64 0 := hx
  have hmem : x ∈ (jst I O ∅ ∅).prs := by
    show x ∈ cfgFlags (I ∪ O) ∅
    rw [cfgFlags_mem, GMap.elem_of_union]; exact .inl (.inr hO)
  simp only [applyOne, ite_eq_right hx', 
    show (W32 1 : w32) ≠ W32 0 by decide, show (W32 1 : w32) ≠ W32 3 by decide,
    ↓reduceIte, removeM, ite_eq_left hmem]
  rw [ite_eq_left (show x ∈ (jst I O ∅ ∅).cfg.outgoing from hO)]
  simp only [jst, removeCfg, GMap.delete_empty, Option.some.injEq, CCState.mk.injEq, true_and]
  congr 1
  apply GMap.set_eq; intro k
  rw [GMap.elem_of_union, GMap.elem_of_union, gm_mem_delete]
  by_cases hk : k = x
  · subst hk; simp [hO]
  · simp [hk]

theorem applyOne_addNodeJ (I O : GSet w64) (x : w64) (hx : x ≠ W64 0) :
    applyOne (addNodeCC x) (jst I O ∅ ∅) = some (jst (<[x := ()]> I) O ∅ ∅) := by
  have hx' : (addNodeCC x).NodeId' ≠ W64 0 := hx
  have hxL : x ∉ (∅ : GSet w64) := GMap.not_elem_of_empty _
  have eU : (<[x := ()]> I ∪ O : GSet w64) = <[x := ()]> (I ∪ O) := GMap.set_eq fun k => by
    rw [GMap.elem_of_union, gset_mem_insert, gset_mem_insert, GMap.elem_of_union, or_assoc]
  have hf : <[x := false]> (cfgFlags (I ∪ O) ∅) = cfgFlags (<[x := ()]> I ∪ O) ∅ := by
    rw [eU, cfgFlags_insert_voter _ _ x hxL]
  simp only [applyOne, ite_eq_right hx', ↓reduceIte,
    makeVoterM]
  split
  · simp only [jst, GMap.delete_empty, Option.some.injEq, CCState.mk.injEq, true_and]
    exact hf
  · simp only [jst, initProgressM, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
      CCState.mk.injEq, true_and]
    exact hf

theorem applyOne_addLearnerJ (I O L : GSet w64) (x : w64) (hx : x ≠ W64 0) (hI : x ∉ I)
    (hO : x ∉ O) :
    applyOne (addLearnerCC x) (jst I O L ∅) = some (jst I O (<[x := ()]> L) ∅) := by
  have hx' : (addLearnerCC x).NodeId' ≠ W64 0 := hx
  have hV : x ∉ (I ∪ O : GSet w64) := by rw [GMap.elem_of_union]; exact fun h => h.elim hI hO
  simp only [applyOne, ite_eq_right hx', 
    show (W32 3 : w32) ≠ W32 0 by decide, ↓reduceIte, makeLearnerM]
  have hlk := cfgFlags_lookup (I ∪ O) L x
  rw [ite_eq_right hV] at hlk
  by_cases hl : x ∈ L
  · rw [ite_eq_left hl] at hlk
    simp only [jst] at hlk ⊢
    rw [hlk]
    simp only
    rw [GMap.insert_id L x () ((GMap.elem_of_gset _ _).1 hl)]
  · rw [ite_eq_right hl] at hlk
    simp only [jst] at hlk ⊢
    rw [hlk]
    simp only [initProgressM, ↓reduceIte, Option.some.injEq, CCState.mk.injEq, true_and]
    exact cfgFlags_insert_learner _ _ x hV

theorem applyOne_addStaged (I O L N : GSet w64) (x : w64) (hx : x ≠ W64 0) (hO : x ∈ O)
    (hI : x ∉ I) (hL : x ∉ L) :
    applyOne (addLearnerCC x) (jst I O L N) = some (jst I O L (<[x := ()]> N)) := by
  have hx' : (addLearnerCC x).NodeId' ≠ W64 0 := hx
  have hlk : (jst I O L N).prs !! x = some false := by
    show cfgFlags (I ∪ O) L !! x = some false
    rw [cfgFlags_lookup, ite_eq_left (by rw [GMap.elem_of_union]; exact .inr hO)]
  simp only [applyOne, ite_eq_right hx', 
    show (W32 3 : w32) ≠ W32 0 by decide, ↓reduceIte, makeLearnerM, hlk]
  rw [ite_eq_left (show x ∈ (jst I O L N).cfg.outgoing from hO)]
  simp only [jst, removeCfg, Option.some.injEq, CCState.mk.injEq, and_true, CfgM.mk.injEq,
    true_and]
  refine ⟨GMap.delete_notin _ _ (gset_lookup_none _ _ hI),
    GMap.delete_notin _ _ (gset_lookup_none _ _ hL), ?_⟩
  apply GMap.set_eq; intro k
  rw [gset_mem_insert, gset_mem_insert, gm_mem_delete]
  by_cases hk : k = x <;> simp [hk]

theorem applyAll_removes (vo : List w64) (I O : GSet w64)
    (H : ∀ x, x ∈ vo → x ≠ W64 0 ∧ x ∈ O) :
    ∃ I', (∀ k, k ∈ I' ↔ k ∈ I ∧ k ∉ vo) ∧
      applyAll (vo.map removeNodeCC) (jst I O ∅ ∅) = some (jst I' O ∅ ∅) := by
  induction vo generalizing I with
  | nil => exact ⟨I, fun k => by simp, rfl⟩
  | cons x xs ih =>
    obtain ⟨hx0, hxO⟩ := H x (by simp)
    obtain ⟨I', HI', Hf⟩ := ih (GMap.delete x I) (fun y hy => H y (List.mem_cons_of_mem _ hy))
    refine ⟨I', fun k => ?_, ?_⟩
    · rw [HI', gm_mem_delete, List.mem_cons, not_or]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h2, h1, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
    · simp only [List.map_cons, applyAll]
      rw [applyOne_remove I O x hx0 hxO]
      exact Hf

theorem applyAll_addNodesJ (v : List w64) (I O : GSet w64)
    (H : ∀ x, x ∈ v → x ≠ W64 0) :
    ∃ I', (∀ k, k ∈ I' ↔ k ∈ I ∨ k ∈ v) ∧
      applyAll (v.map addNodeCC) (jst I O ∅ ∅) = some (jst I' O ∅ ∅) := by
  induction v generalizing I with
  | nil => exact ⟨I, fun k => by simp, rfl⟩
  | cons x xs ih =>
    obtain ⟨I', HI', Hf⟩ := ih (<[x := ()]> I) (fun y hy => H y (List.mem_cons_of_mem _ hy))
    refine ⟨I', fun k => ?_, ?_⟩
    · rw [HI', gset_mem_insert, List.mem_cons]; simp only [or_assoc, or_comm]
    · simp only [List.map_cons, applyAll]
      rw [applyOne_addNodeJ I O x (H x (by simp))]
      exact Hf

theorem applyAll_addLearnersJ (l : List w64) (I O L : GSet w64)
    (H : ∀ x, x ∈ l → x ≠ W64 0 ∧ x ∉ I ∧ x ∉ O) :
    ∃ L', (∀ k, k ∈ L' ↔ k ∈ L ∨ k ∈ l) ∧
      applyAll (l.map addLearnerCC) (jst I O L ∅) = some (jst I O L' ∅) := by
  induction l generalizing L with
  | nil => exact ⟨L, fun k => by simp, rfl⟩
  | cons x xs ih =>
    obtain ⟨hx0, hxI, hxO⟩ := H x (by simp)
    obtain ⟨L', HL', Hf⟩ := ih (<[x := ()]> L) (fun y hy => H y (List.mem_cons_of_mem _ hy))
    refine ⟨L', fun k => ?_, ?_⟩
    · rw [HL', gset_mem_insert, List.mem_cons]; simp only [or_assoc, or_comm]
    · simp only [List.map_cons, applyAll]
      rw [applyOne_addLearnerJ I O L x hx0 hxI hxO]
      exact Hf

theorem applyAll_addStaged (ln : List w64) (I O L N : GSet w64)
    (H : ∀ x, x ∈ ln → x ≠ W64 0 ∧ x ∈ O ∧ x ∉ I ∧ x ∉ L) :
    ∃ N', (∀ k, k ∈ N' ↔ k ∈ N ∨ k ∈ ln) ∧
      applyAll (ln.map addLearnerCC) (jst I O L N) = some (jst I O L N') := by
  induction ln generalizing N with
  | nil => exact ⟨N, fun k => by simp, rfl⟩
  | cons x xs ih =>
    obtain ⟨hx0, hxO, hxI, hxL⟩ := H x (by simp)
    obtain ⟨N', HN', Hf⟩ := ih (<[x := ()]> N) (fun y hy => H y (List.mem_cons_of_mem _ hy))
    refine ⟨N', fun k => ?_, ?_⟩
    · rw [HN', gset_mem_insert, List.mem_cons]; simp only [or_assoc, or_comm]
    · simp only [List.map_cons, applyAll]
      rw [applyOne_addStaged I O L N x hx0 hxO hxI hxL]
      exact Hf

/-- `EnterJoint(al, restoreInCC ...)` on the outgoing voters as a simple configuration. -/
theorem enterJointM_restoreIn (vo v l ln : List w64) (al : Bool) (Hwf : CSWf vo v l ln)
    (hvo : vo ≠ []) :
    enterJointM al (restoreInCC vo v l ln) (cfgState (GMap.listToSet vo) ∅) =
      some (cfgStateC (csCfgM vo v l ln al)) := by
  obtain ⟨hv, H0, Hl, Hn, -⟩ := Hwf
  obtain ⟨O, hO⟩ : ∃ O, GMap.listToSet vo = O := ⟨_, rfl⟩
  rw [hO]
  have mO : ∀ k, k ∈ O ↔ k ∈ vo := fun k => by rw [← hO]; exact GMap.elem_of_list_to_set _ _
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil vo hvo
  have hOne : O ≠ ∅ := gset_ne_empty_of_mem ((mO x0).2 hx0)
  -- the start: the outgoing voters copied into both halves
  have Hstart : ∀ s0 : CCState, s0 = cfgState O ∅ →
      CCState.mk { s0.cfg with outgoing := s0.cfg.incoming, autoLeave := false } s0.prs =
        jst O O ∅ ∅ := by
    rintro s0 rfl
    simp only [cfgState, cfgM, jst, CCState.mk.injEq, true_and]
    congr 1
    exact GMap.set_eq fun k => by rw [GMap.elem_of_union, or_self]
  obtain ⟨I1, HI1, Hf1⟩ := applyAll_removes vo O O
    (fun x hx => ⟨H0 x (.inl hx), (mO x).2 hx⟩)
  obtain ⟨I2, HI2, Hf2⟩ := applyAll_addNodesJ v I1 O (fun x hx => H0 x (.inr (.inl hx)))
  have eI2 : ∀ k, k ∈ I2 ↔ k ∈ v := fun k => by
    rw [HI2, HI1, mO]
    exact ⟨fun h => h.elim (fun h' => absurd h'.1 h'.2) id, .inr⟩
  obtain ⟨L3, HL3, Hf3⟩ := applyAll_addLearnersJ l I2 O ∅
    (fun x hx => ⟨H0 x (.inr (.inr (.inl hx))), by rw [eI2]; exact (Hl x hx).1,
      by rw [mO]; exact (Hl x hx).2⟩)
  have eL3 : ∀ k, k ∈ L3 ↔ k ∈ l := fun k => by
    rw [HL3]; exact ⟨fun h => h.elim (fun h' => absurd h' (GMap.not_elem_of_empty _)) id, .inr⟩
  obtain ⟨N4, HN4, Hf4⟩ := applyAll_addStaged ln I2 O L3 ∅
    (fun x hx => ⟨H0 x (.inr (.inr (.inr hx))), (mO x).2 (Hn x hx).1,
      by rw [eI2]; exact (Hn x hx).2.1, by rw [eL3]; exact (Hn x hx).2.2⟩)
  have eN4 : ∀ k, k ∈ N4 ↔ k ∈ ln := fun k => by
    rw [HN4]; exact ⟨fun h => h.elim (fun h' => absurd h' (GMap.not_elem_of_empty _)) id, .inr⟩
  have Happ : applyAll (restoreInCC vo v l ln) (jst O O ∅ ∅) = some (jst I2 O L3 N4) := by
    simp only [restoreInCC]
    rw [applyAll_append, applyAll_append, applyAll_append, Hf1]
    simp only [Option.bind_some]
    rw [Hf2]; simp only [Option.bind_some]
    rw [Hf3]; simp only [Option.bind_some]
    exact Hf4
  obtain ⟨y0, hy0⟩ := List.exists_mem_of_ne_nil v hv
  have hI2ne : I2 ≠ ∅ := gset_ne_empty_of_mem ((eI2 y0).2 hy0)
  have HappM : applyM (restoreInCC vo v l ln) (jst O O ∅ ∅) = some (jst I2 O L3 N4) := by
    simp only [applyM, Happ, Option.bind_some]
    rw [ite_eq_right (show (jst I2 O L3 N4).cfg.incoming ≠ ∅ from hI2ne)]
  have eI : I2 = GMap.listToSet v := GMap.set_eq fun k => by rw [eI2, GMap.elem_of_list_to_set]
  have eL : L3 = GMap.listToSet l := GMap.set_eq fun k => by rw [eL3, GMap.elem_of_list_to_set]
  have eN : N4 = GMap.listToSet ln := GMap.set_eq fun k => by rw [eN4, GMap.elem_of_list_to_set]
  subst eI eL eN
  -- `checkAndReturn` with `AutoLeave` set
  have Hres : ∀ s1 : CCState,
      s1 = jst (GMap.listToSet v) O (GMap.listToSet l) (GMap.listToSet ln) →
      CCState.mk { s1.cfg with autoLeave := al } s1.prs = cfgStateC (csCfgM vo v l ln al) := by
    rintro s1 rfl
    simp only [jst, cfgStateC, csCfgM, ite_eq_right hvo, hO]
    rfl
  have Hinv : CfgInv (cfgStateC (csCfgM vo v l ln al)) := by
    simp only [cfgStateC, csCfgM, ite_eq_right hvo, hO]
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun h => absurd h hOne⟩
    · show k ∈ cfgFlags _ _
      rw [cfgFlags_mem, CfgM.voters, GMap.elem_of_union]
      simp only at hk
      rcases hk with hk | hk | hk | hk
      · exact .inl (.inl hk)
      · exact .inl (.inr hk)
      · exact .inr hk
      · exact .inl (.inr ((mO k).2 (Hn k ((GMap.elem_of_list_to_set _ _).1 hk)).1))
    · simp only at hk ⊢
      have h := Hn k ((GMap.elem_of_list_to_set _ _).1 hk)
      refine ⟨(mO k).2 h.1, ?_⟩
      rw [cfgFlags_lookup, ite_eq_left]
      rw [CfgM.voters, GMap.elem_of_union]; exact .inr ((mO k).2 h.1)
    · simp only at hk ⊢
      have h := Hl k ((GMap.elem_of_list_to_set _ _).1 hk)
      have h1 : k ∉ O := fun h' => h.2 ((mO k).1 h')
      have h2 : k ∉ GMap.listToSet v := fun h' => h.1 ((GMap.elem_of_list_to_set _ _).1 h')
      refine ⟨h1, h2, ?_⟩
      rw [cfgFlags_lookup, ite_eq_right (fun h' => by
        rw [CfgM.voters, GMap.elem_of_union] at h'; exact h'.elim h2 h1), ite_eq_left hk]
  unfold enterJointM
  rw [clearAutoLeave_cfgState, ite_eq_right (fun h => h (cfgInv_cfgState O ∅
    (fun k hk => absurd hk (GMap.not_elem_of_empty _)))),
    ite_eq_right (fun h => h rfl), ite_eq_right (show (cfgState O ∅).cfg.incoming ≠ ∅ from hOne), Hstart _ rfl,
    HappM]
  simp only
  rw [Hres _ rfl]
  simp [checkedM, Hinv]

/-- `Restore` of a well-formed `ConfState` answers the configuration it denotes. -/
theorem restoreM_wf (vo v l ln : List w64) (al : Bool) (Hwf : CSWf vo v l ln) :
    restoreM vo v l ln al = some (cfgStateC (csCfgM vo v l ln al)) := by
  unfold restoreM restoreSimpleOps
  by_cases hvo : vo = []
  · subst hvo
    obtain ⟨hv, H0, Hl, -, Hln⟩ := Hwf
    have hln := Hln rfl
    subst hln
    simp only [↓reduceIte]
    rw [simpleFold_restoreIn v l hv (fun x hx => H0 x (.inr (hx.elim .inl (.inr ∘ .inl))))
      (fun x hx => (Hl x hx).1)]
    simp only [cfgState, cfgStateC, csCfgM, ↓reduceIte, cfgM, Option.some.injEq,
      CCState.mk.injEq]
    rw [CfgM.voters]
    simp only [show GMap.listToSet ([] : List w64) = ∅ from rfl, GMap.union_empty_r_L, and_self]
  · simp only [hvo, ↓reduceIte]
    have H0 := Hwf.2.1
    obtain ⟨V', HV', -, Hf⟩ := simpleFold_addNodes vo ∅ ∅
      (fun x hx => ⟨H0 x (.inl hx), GMap.not_elem_of_empty _⟩)
      (fun k hk => absurd hk (GMap.not_elem_of_empty _))
    have eV : V' = GMap.listToSet vo := GMap.set_eq fun k => by
      rw [HV', GMap.elem_of_list_to_set]
      exact ⟨fun h => h.elim (fun h' => absurd h' (GMap.not_elem_of_empty _)) id, .inr⟩
    subst eV
    rw [restoreOutCC, Hf]
    simp only [Option.bind_some]
    exact enterJointM_restoreIn vo v l ln al Hwf hvo

/-- The configuration a well-formed `ConfState` denotes passes `checkInvariants`. -/
theorem restoreM_cfgInv {vo v l ln : List w64} {al : Bool} {s : CCState}
    (H : restoreM vo v l ln al = some s) : CfgInv s := by
  unfold restoreM at H
  split at H
  · -- the last `Simple` checked it; with no op at all the empty state passes trivially
    revert H
    generalize restoreSimpleOps vo v l ln = ops
    suffices ∀ s0, CfgInv s0 → simpleFold ops s0 = some s → CfgInv s by
      exact this _ (cfgInv_cfgState ∅ ∅ (fun k hk => absurd hk (GMap.not_elem_of_empty _)))
    induction ops with
    | nil => intro s0 h0 H; cases H; exact h0
    | cons c cs ih =>
      intro s0 _ H
      simp only [simpleFold] at H
      cases h1 : simpleM [c] s0 with
      | none => rw [h1] at H; cases H
      | some s1 =>
        rw [h1] at H
        refine ih s1 ?_ H
        unfold simpleM at h1
        split at h1; · cases h1
        split at h1; · cases h1
        split at h1; · cases h1
        split at h1; · cases h1
        obtain ⟨rfl, h⟩ := checkedM_some h1
        exact h
  · cases h1 : simpleFold (restoreSimpleOps vo v l ln) (cfgState ∅ ∅) with
    | none => rw [h1] at H; cases H
    | some s1 =>
      rw [h1] at H
      simp only [Option.bind_some] at H
      unfold enterJointM at H
      split at H; · cases H
      split at H; · cases H
      split at H; · cases H
      split at H; · cases H
      obtain ⟨rfl, h⟩ := checkedM_some H
      exact h

end model

end EtcdGrove
end Perennial
