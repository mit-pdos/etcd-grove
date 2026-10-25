/-
The model of applying a configuration change (raft v3.7 retarget, stage R1): the pure part
of `InvApplyConf.lean` of the old proof (its `section model`, verbatim but for R1's type
rename), split off so that the model (`Protocol/CfgOverlap`) does not import the physical
predicates the file's heap section needs (`InvRaftPhys`). The heap section (`progRAt`,
`ownTracker_toCC`, `ownResult_noop_transfer`) is ported with the raft layer (stages R2/R4),
importing this file. `CCApplyC.lean` is the same split of `InvApplyConfC.lean`.

From `InvApplyConf.lean` (2026-10-13, reconfiguration stage D): the model of
`applyConfChange`'s choice (`ccApplyM`: `LeaveJoint`, `EnterJoint` or `Simple`, on the
`ConfChangeV2` that `AsV2` makes of the change, `ccV2Of`), and the state `confchange` sees of
the node's configuration (`cfgState cfg`: the voters `cfg`, nothing else, every tracked
`Progress` a non-learner). Only `Simple` can answer the same state (`ccApplyM_noop`), e.g. for
a change with `NodeId = 0`, which `Changer.apply` skips (`ccApplyM_single_noop`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC
public import RaftWitness.Proof.go_etcd_io.raft.v3.CCModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The model -/

section model
variable [FfiSyntax]

/-- The voters `cfg` tracked as non-learners and the learners `lrn` as learners (since
2026-10-13, reconfiguration stage L; until then voters only). -/
def cfgFlags (cfg lrn : GSet w64) : GMap w64 Bool :=
  GMap.fmap (fun _ => false) cfg ∪ GMap.fmap (fun _ => true) lrn

/-- The configuration with voters `cfg` and learners `lrn` as a `Config` (the same as
`CfgM.simple cfg lrn`, `Protocol/StepC.lean`: `cfgM_eq_simple`). -/
def cfgM (cfg lrn : GSet w64) : CfgM :=
  { incoming := cfg, outgoing := ∅, learners := lrn, learnersNext := ∅, autoLeave := false }

theorem cfgM_eq_simple (cfg lrn : GSet w64) : cfgM cfg lrn = CfgM.simple cfg lrn := rfl

/-- What `confchange` sees of a node whose configuration is `cfg` with the learners `lrn`
(`ownTracker`: `lrn` is the tracked ids outside `cfg`). -/
def cfgState (cfg lrn : GSet w64) : CCState := { cfg := cfgM cfg lrn, prs := cfgFlags cfg lrn }

/-- What `ConfChangeI.AsV2()` makes of a change: a `ConfChange` is one change with
transition `Auto` (`ConfChange.AsV2`'s spec); a `ConfChangeV2` is itself. -/
def ccV2Of : CCMsg → raftpb.ConfChangeTransition × List ConfChangeSingleM
  | .v1 m => (W32 0, [{ Type' := m.type, NodeId' := m.nodeId }])
  | .v2 m => (m.transition, m.changes)

/-- `raft.applyConfChange`'s choice (raft.go): `LeaveJoint` for an empty `Auto` change,
else `EnterJoint` when `ConfChangeV2.EnterJoint` says so, else `Simple`; `none` where
`EnterJoint` panics (an undefined transition with joint consensus). -/
def ccApplyM (t : raftpb.ConfChangeTransition) (ccs : List ConfChangeSingleM)
    (s : CCState) : Option CCState :=
  if t = W32 0 ∧ ccs = [] then leaveJointM s
  else match enterJointOf t ccs.length with
    | some (al, true) => enterJointM al ccs s
    | some (_, false) => simpleM ccs s
    | none => none

/-! `confchange` and the witness (2026-10-20). Without an `AddWitness` a change keeps the
configuration's witness or clears it (`remove` of the witness clears `Witnesses[0]`;
`leaveJointState` keeps it), so a witness-free configuration stays witness-free. -/

/-- No `AddWitness` among the changes (`apply` skips a change of node `0`). -/
def NoAddWit (ccs : List ConfChangeSingleM) : Prop :=
  ∀ c ∈ ccs, c.NodeId' ≠ W64 0 → c.Type' ≠ W32 4

instance NoAddWit.decidable (ccs : List ConfChangeSingleM) : Decidable (NoAddWit ccs) := by
  unfold NoAddWit; infer_instance

theorem removeM_wit (id : w64) (s : CCState) :
    (removeM id s).cfg.wit = s.cfg.wit ∨ (removeM id s).cfg.wit = W64 0 := by
  unfold removeM removeCfg
  split
  · simp only
    split
    · exact .inr rfl
    · exact .inl rfl
  · exact .inl rfl

theorem makeLearnerM_wit (id : w64) (s : CCState) :
    (makeLearnerM id s).cfg.wit = s.cfg.wit ∨ (makeLearnerM id s).cfg.wit = W64 0 := by
  unfold makeLearnerM initProgressM
  split
  · exact .inl rfl
  · exact .inl rfl
  · split
    · simp only [removeCfg]
      split
      · exact .inr rfl
      · exact .inl rfl
    · simp only [removeCfg]
      split
      · exact .inr rfl
      · exact .inl rfl

theorem applyOne_wit {cc : ConfChangeSingleM} {s s' : CCState} (h : applyOne cc s = some s')
    (h4 : cc.NodeId' ≠ W64 0 → cc.Type' ≠ W32 4) :
    s'.cfg.wit = s.cfg.wit ∨ s'.cfg.wit = W64 0 := by
  unfold applyOne at h
  split at h
  · cases h; exact .inl rfl
  rename_i h0
  split at h
  · unfold makeVoterO at h
    split at h
    · cases h
    · cases h; exact .inl (makeVoterM_shape _ _).2
  split at h
  · unfold makeLearnerO at h
    split at h
    · cases h
    · cases h; exact makeLearnerM_wit _ _
  split at h
  · cases h; exact removeM_wit _ _
  split at h
  · cases h; exact .inl rfl
  split at h
  · rename_i h4'; exact absurd h4' (h4 h0)
  · cases h

theorem applyAll_wit {ccs : List ConfChangeSingleM} {s s' : CCState}
    (h : applyAll ccs s = some s') (h4 : NoAddWit ccs) :
    s'.cfg.wit = s.cfg.wit ∨ s'.cfg.wit = W64 0 := by
  induction ccs generalizing s with
  | nil => simp only [applyAll, Option.some.injEq] at h; subst h; exact .inl rfl
  | cons cc ccs ih =>
    simp only [applyAll] at h
    cases h1 : applyOne cc s with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      have e1 := applyOne_wit h1 (h4 cc (List.mem_cons_self ..))
      rcases ih h (fun c hc => h4 c (List.mem_cons_of_mem _ hc)) with e | e
      · rw [e]; exact e1
      · exact .inr e

theorem applyM_wit {ccs : List ConfChangeSingleM} {s s' : CCState}
    (h : applyM ccs s = some s') (h4 : NoAddWit ccs) :
    s'.cfg.wit = s.cfg.wit ∨ s'.cfg.wit = W64 0 := by
  unfold applyM at h
  cases h1 : applyAll ccs s with
  | none => rw [h1] at h; cases h
  | some s1 =>
    rw [h1] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; exact applyAll_wit h1 h4

/-- Without an `AddWitness` a change keeps the witness or clears it. -/
theorem ccApplyM_wit {t : raftpb.ConfChangeTransition} {ccs : List ConfChangeSingleM}
    {s s' : CCState} (h4 : NoAddWit ccs) (h : ccApplyM t ccs s = some s') :
    s'.cfg.wit = s.cfg.wit ∨ s'.cfg.wit = W64 0 := by
  unfold ccApplyM at h
  split at h
  · unfold leaveJointM at h
    split at h
    · cases h
    split at h
    · cases h
    obtain ⟨rfl, -⟩ := checkedM_some h
    left; rfl
  · split at h
    · unfold enterJointM at h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      rename_i s2 hs2
      obtain ⟨rfl, -⟩ := checkedM_some h
      have e := applyM_wit hs2 h4
      exact e
    · unfold simpleM at h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      rename_i s2 hs2
      split at h
      · cases h
      obtain ⟨rfl, -⟩ := checkedM_some h
      have e := applyM_wit hs2 h4
      exact e
    · cases h

/-- A witness-free configuration stays witness-free, without an `AddWitness`. -/
theorem ccApplyM_wit0 {t : raftpb.ConfChangeTransition} {ccs : List ConfChangeSingleM}
    {s s' : CCState} (h0 : s.cfg.wit = W64 0) (h4 : NoAddWit ccs) (h : ccApplyM t ccs s = some s') :
    s'.cfg.wit = W64 0 := by
  rcases ccApplyM_wit h4 h with e | e
  · rw [e]; exact h0
  · exact e

/-- A change that leaves every configuration with the voters `cfg` as it is, whatever its
learners (2026-10-13): the scope of `RawNode.ApplyConfChange`, whose state does not say
which learners the node tracks. -/
def CCNoop (cfg : GSet w64) (t : raftpb.ConfChangeTransition)
    (ccs : List ConfChangeSingleM) : Prop :=
  ∀ lrn : GSet w64, (∀ k, k ∈ lrn → k ∉ cfg) →
    ccApplyM t ccs (cfgState cfg lrn) = some (cfgState cfg lrn)

theorem cfgFlags_lookup (cfg lrn : GSet w64) (k : w64) :
    cfgFlags cfg lrn !! k =
      if k ∈ cfg then some false else if k ∈ lrn then some true else none := by
  simp only [cfgFlags, GMap.lookup_union, GMap.lookup_fmap]
  cases h1 : cfg !! k with
  | some u =>
    have hk : k ∈ cfg := (GMap.elem_of_gset _ _).2 (by cases u; exact h1)
    simp [hk]
  | none =>
    have hk : k ∉ cfg := fun h => by rw [GMap.elem_of_gset, h1] at h; cases h
    cases h2 : lrn !! k with
    | some u =>
      have hl : k ∈ lrn := (GMap.elem_of_gset _ _).2 (by cases u; exact h2)
      simp [hk, hl]
    | none =>
      have hl : k ∉ lrn := fun h => by rw [GMap.elem_of_gset, h2] at h; cases h
      simp [hk, hl]

theorem cfgFlags_mem (cfg lrn : GSet w64) (k : w64) :
    k ∈ cfgFlags cfg lrn ↔ k ∈ cfg ∨ k ∈ lrn := by
  rw [GMap.mem_iff, cfgFlags_lookup]
  by_cases h1 : k ∈ cfg
  · simp [h1]
  · by_cases h2 : k ∈ lrn <;> simp [h1, h2]

theorem cfgInv_cfgState (cfg lrn : GSet w64) (Hd : ∀ k, k ∈ lrn → k ∉ cfg) :
    CfgInv (cfgState cfg lrn) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun _ => ⟨rfl, rfl⟩⟩
  · show k ∈ cfgFlags cfg lrn
    rw [cfgFlags_mem]
    rcases hk with hk | hk | hk | hk
    · exact .inl hk
    · exact absurd hk (GMap.not_elem_of_empty _)
    · exact .inr hk
    · exact absurd hk (GMap.not_elem_of_empty _)
  · exact absurd hk (GMap.not_elem_of_empty _)
  · refine ⟨GMap.not_elem_of_empty _, Hd k hk, ?_⟩
    show cfgFlags cfg lrn !! k = some true
    rw [cfgFlags_lookup, ite_eq_right (Hd k hk), ite_eq_left (show k ∈ lrn from hk)]

theorem clearAutoLeave_cfgState (cfg lrn : GSet w64) :
    clearAutoLeave (cfgState cfg lrn) = cfgState cfg lrn := rfl

theorem applyOne_outgoing (c : ConfChangeSingleM) (s s' : CCState)
    (h : applyOne c s = some s') : s'.cfg.outgoing = s.cfg.outgoing :=
  (applyOne_shape h).1

theorem applyAll_outgoing (ccs : List ConfChangeSingleM) (s s' : CCState)
    (h : applyAll ccs s = some s') : s'.cfg.outgoing = s.cfg.outgoing := by
  induction ccs generalizing s with
  | nil => simp only [applyAll, Option.some.injEq] at h; rw [h]
  | cons c ccs ih =>
    simp only [applyAll] at h
    cases h1 : applyOne c s with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1, Option.bind_some] at h
      rw [ih s1 h, applyOne_outgoing c s s1 h1]

theorem applyM_outgoing (ccs : List ConfChangeSingleM) (s s' : CCState)
    (h : applyM ccs s = some s') : s'.cfg.outgoing = s.cfg.outgoing := by
  unfold applyM at h
  cases h1 : applyAll ccs s with
  | none => rw [h1] at h; cases h
  | some s1 =>
    rw [h1, Option.bind_some] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; exact applyAll_outgoing ccs s _ h1

/-- A change whose model answer is the configuration it started from is a `Simple` one:
`LeaveJoint` fails on a non-joint configuration, and `EnterJoint` answers a joint one. -/
theorem ccApplyM_noop (cfg lrn : GSet w64) (Hd : ∀ k, k ∈ lrn → k ∉ cfg)
    (t : raftpb.ConfChangeTransition) (ccs : List ConfChangeSingleM)
    (H : ccApplyM t ccs (cfgState cfg lrn) = some (cfgState cfg lrn)) :
    ¬ (t = W32 0 ∧ ccs = []) ∧ (∃ al, enterJointOf t ccs.length = some (al, false)) ∧
      simpleM ccs (cfgState cfg lrn) = some (cfgState cfg lrn) := by
  unfold ccApplyM at H
  by_cases Hl : t = W32 0 ∧ ccs = []
  · rw [ite_eq_left Hl] at H
    unfold leaveJointM at H
    rw [ite_eq_right (fun h => h (cfgInv_cfgState cfg lrn Hd)),
      ite_eq_left (show (cfgState cfg lrn).cfg.outgoing = ∅ from rfl)] at H
    cases H
  rw [ite_eq_right Hl] at H
  refine ⟨Hl, ?_⟩
  rcases He : enterJointOf t ccs.length with _ | ⟨al, ok⟩
  · rw [He] at H; cases H
  rw [He] at H
  cases ok
  · exact ⟨⟨al, rfl⟩, H⟩
  · exfalso
    simp only at H
    unfold enterJointM at H
    rw [ite_eq_right (fun h => h (cfgInv_cfgState cfg lrn Hd)), ite_eq_right (fun h => h rfl)] at H
    by_cases Hin : (cfgState cfg lrn).cfg.incoming = ∅
    · rw [ite_eq_left Hin] at H; cases H
    rw [ite_eq_right Hin] at H
    revert H
    generalize Happ : applyM ccs _ = r
    cases r with
    | none => intro H; cases H
    | some s1 =>
      intro H
      simp only [checkedM] at H
      split at H
      · simp only [Option.some.injEq] at H
        have Hout := applyM_outgoing ccs _ s1 Happ
        have h2 : s1.cfg.outgoing = (cfgState cfg lrn).cfg.outgoing := by rw [← H]
        rw [h2] at Hout
        exact Hin Hout.symm
      · cases H

/-- A single change with `NodeId = 0` and transition `Auto` (what `ConfChange.AsV2` makes of
any `ConfChange` with `NodeId = 0`) leaves a non-empty configuration as it is:
`Changer.apply` skips it. -/
theorem ccApplyM_single_noop (cfg lrn : GSet w64) (Hd : ∀ k, k ∈ lrn → k ∉ cfg)
    (c : ConfChangeSingleM) (Hc : c.NodeId' = W64 0) (Hne : cfg ≠ ∅) :
    ccApplyM (W32 0) [c] (cfgState cfg lrn) = some (cfgState cfg lrn) := by
  have Happ : applyM [c] (cfgState cfg lrn) = some (cfgState cfg lrn) := by
    simp only [applyM, applyAll, applyOne, Hc, ↓reduceIte, Option.bind_some]
    rw [ite_eq_right (by exact Hne)]
  have Hsd : ¬ SymdiffTooBig cfg cfg := by
    unfold SymdiffTooBig symdiffN
    rw [GMap.map_difference_diag, GMap.map_size_empty]
    decide
  have Hs : simpleM [c] (cfgState cfg lrn) = some (cfgState cfg lrn) := by
    unfold simpleM
    rw [clearAutoLeave_cfgState, ite_eq_right (fun h => h (cfgInv_cfgState cfg lrn Hd)),
      ite_eq_right (fun h => h rfl), Happ]
    simp only
    rw [ite_eq_right (show ¬ SymdiffTooBig (cfgState cfg lrn).cfg.incoming
      (cfgState cfg lrn).cfg.incoming from Hsd)]
    simp [checkedM, cfgInv_cfgState cfg lrn Hd]
  unfold ccApplyM
  rw [ite_eq_right (by simp)]
  have He : enterJointOf (W32 0) [c].length = some (false, false) := by
    simp [enterJointOf]
  rw [He]
  exact Hs

/-- A `ConfChange` with `NodeId = 0`, whatever the learners. -/
theorem ccApplyM_v1_noop (cfg : GSet w64) (m : CCV1M) (H : m.nodeId = W64 0) (Hne : cfg ≠ ∅) :
    CCNoop cfg (ccV2Of (.v1 m)).1 (ccV2Of (.v1 m)).2 :=
  fun lrn Hd => ccApplyM_single_noop cfg lrn Hd _ H Hne


/-! ### `Restore`'s steps on a non-joint configuration (2026-10-13, stage L)

`confchange.Restore` replays a `ConfState` as one `Simple` per voter (`AddNode`), then one per
learner (`AddLearnerNode`); on `cfgState V L` each adds the id to the voters, or the
learners. -/

theorem cfgFlags_insert_voter (V L : GSet w64) (id : w64) (h : id ∉ L) :
    <[id := false]> (cfgFlags V L) = cfgFlags (<[id := ()]> V) L := by
  apply GMap.map_eq; intro k
  rw [cfgFlags_lookup]
  by_cases hk : id = k
  · subst hk
    rw [GMap.lookup_insert_eq, ite_eq_left ((GMap.elem_of_gset _ _).2 (GMap.lookup_insert_eq _ _ _))]
  · rw [GMap.lookup_insert_ne _ _ hk, cfgFlags_lookup]
    have e : k ∈ (<[id := ()]> V : GSet w64) ↔ k ∈ V := by
      rw [GMap.elem_of_gset, GMap.elem_of_gset, GMap.lookup_insert_ne _ _ hk]
    by_cases h1 : k ∈ V
    · rw [ite_eq_left h1, ite_eq_left (e.2 h1)]
    · rw [ite_eq_right h1, ite_eq_right (fun h' => h1 (e.1 h'))]

theorem cfgFlags_insert_learner (V L : GSet w64) (id : w64) (h : id ∉ V) :
    <[id := true]> (cfgFlags V L) = cfgFlags V (<[id := ()]> L) := by
  apply GMap.map_eq; intro k
  rw [cfgFlags_lookup]
  by_cases hk : id = k
  · subst hk
    rw [GMap.lookup_insert_eq, ite_eq_right h,
      ite_eq_left ((GMap.elem_of_gset _ _).2 (GMap.lookup_insert_eq _ _ _))]
  · rw [GMap.lookup_insert_ne _ _ hk, cfgFlags_lookup]
    have e : k ∈ (<[id := ()]> L : GSet w64) ↔ k ∈ L := by
      rw [GMap.elem_of_gset, GMap.elem_of_gset, GMap.lookup_insert_ne _ _ hk]
    by_cases h1 : k ∈ V
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : k ∈ L
      · rw [ite_eq_left h2, ite_eq_left (e.2 h2)]
      · rw [ite_eq_right h2, ite_eq_right (fun h' => h2 (e.1 h'))]

theorem gset_lookup_none (L : GSet w64) (id : w64) (h : id ∉ L) : L !! id = none := by
  cases hl : L !! id with
  | none => rfl
  | some u => exact absurd ((GMap.elem_of_gset _ _).2 (by cases u; exact hl)) h

theorem gset_insert_ne_empty (V : GSet w64) (id : w64) : (<[id := ()]> V : GSet w64) ≠ ∅ := by
  intro h; have := congrArg (fun m => m !! id) h; simp at this

/-- One voter more changes the voters by at most one. -/
theorem not_symdiffTooBig_insert (V : GSet w64) (id : w64) :
    ¬ SymdiffTooBig V (<[id := ()]> V) := by
  unfold SymdiffTooBig symdiffN
  have h1 : V \ (<[id := ()]> V) = ∅ := by
    apply GMap.map_eq; intro k
    by_cases hk : id = k
    · subst hk; simp
    · rw [GMap.lookup_sdiff, GMap.lookup_insert_ne _ _ hk]
      rcases h : V !! k with _ | v <;> simp
  have h2 : GMap.size ((<[id := ()]> V) \ V) ≤ 1 := by
    have hsub : (<[id := ()]> V) \ V ⊆ ({[id := ()]} : GMap w64 Unit) := by
      intro k v hkv
      by_cases hk : id = k
      · subst hk; cases v; simp
      · rw [GMap.lookup_sdiff, GMap.lookup_insert_ne _ _ hk] at hkv
        rcases h : V !! k with _ | v' <;> simp_all
    have := GMap.map_subseteq_size hsub
    rw [GMap.map_size_singleton] at this
    exact this
  rw [h1, GMap.map_size_empty]
  generalize GMap.size ((<[id := ()]> V) \ V) = n at h2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with h0 | h0 <;> subst h0 <;> decide

/-- `Simple([AddNode id])` on `cfgState V L`, `id` not a learner: `id` joins the voters. -/
theorem simpleM_cfgState_addNode (V L : GSet w64) (id : w64) (hid : id ≠ W64 0)
    (hL : id ∉ L) (Hd : ∀ k, k ∈ L → k ∉ V) :
    simpleM [addNodeCC id] (cfgState V L) = some (cfgState (<[id := ()]> V) L) := by
  have Hd' : ∀ k, k ∈ L → k ∉ (<[id := ()]> V : GSet w64) := by
    intro k hk h
    rcases (gset_mem_insert V id k).1 h with h | h
    · subst h; exact hL hk
    · exact Hd k hk h
  have Hmv : makeVoterM id (cfgState V L) = cfgState (<[id := ()]> V) L := by
    unfold makeVoterM
    split
    · simp only [cfgState, cfgM]
      rw [GMap.delete_notin _ _ (gset_lookup_none L id hL), GMap.delete_empty,
        cfgFlags_insert_voter V L id hL]
    · simp only [initProgressM, cfgState, cfgM, Bool.false_eq_true, ↓reduceIte]
      rw [cfgFlags_insert_voter V L id hL]
  have Happ : applyM [addNodeCC id] (cfgState V L) = some (cfgState (<[id := ()]> V) L) := by
    have hid' : (addNodeCC id).NodeId' ≠ W64 0 := hid
    simp only [applyM, applyAll, applyOne, ite_eq_right hid', ↓reduceIte, Option.bind_some]
    rw [makeVoterO_nw rfl, Hmv]
    try simp only [Option.bind_some]
    rw [ite_eq_right (show (cfgState (<[id := ()]> V) L).cfg.incoming ≠ ∅ from
      gset_insert_ne_empty V id)]
  unfold simpleM
  rw [clearAutoLeave_cfgState, ite_eq_right (fun h => h (cfgInv_cfgState V L Hd)),
    ite_eq_right (fun h => h rfl), Happ]
  simp only
  rw [ite_eq_right (show ¬ SymdiffTooBig (cfgState V L).cfg.incoming
    (cfgState (<[id := ()]> V) L).cfg.incoming from not_symdiffTooBig_insert V id)]
  simp [checkedM, cfgInv_cfgState _ L Hd']

/-- `Simple([AddLearnerNode id])` on `cfgState V L`, `V` non-empty, `id` not a voter: `id`
joins the learners. -/
theorem simpleM_cfgState_addLearner (V L : GSet w64) (id : w64) (hid : id ≠ W64 0)
    (hV : id ∉ V) (hne : V ≠ ∅) (Hd : ∀ k, k ∈ L → k ∉ V) :
    simpleM [addLearnerCC id] (cfgState V L) = some (cfgState V (<[id := ()]> L)) := by
  have Hd' : ∀ k, k ∈ (<[id := ()]> L : GSet w64) → k ∉ V := by
    intro k h
    rcases (gset_mem_insert L id k).1 h with h | h
    · subst h; exact hV
    · exact Hd k h
  have Hml : makeLearnerM id (cfgState V L) = cfgState V (<[id := ()]> L) := by
    unfold makeLearnerM
    have hlk := cfgFlags_lookup V L id
    rw [ite_eq_right hV] at hlk
    by_cases hl : id ∈ L
    · rw [ite_eq_left hl] at hlk
      simp only [cfgState] at hlk ⊢
      rw [hlk]
      simp only
      rw [GMap.insert_id L id () ((GMap.elem_of_gset _ _).1 hl)]
    · rw [ite_eq_right hl] at hlk
      simp only [cfgState] at hlk ⊢
      rw [hlk]
      simp only [initProgressM, cfgM, ↓reduceIte]
      rw [cfgFlags_insert_learner V L id hV]
  have Happ : applyM [addLearnerCC id] (cfgState V L) = some (cfgState V (<[id := ()]> L)) := by
    have hid' : (addLearnerCC id).NodeId' ≠ W64 0 := hid
    simp only [applyM, applyAll, applyOne, ite_eq_right hid', ↓reduceIte]
    rw [ite_eq_right (show (W32 3 : w32) ≠ W32 0 by decide), makeLearnerO_nw rfl, Hml]
    simp only [Option.bind_some]
    rw [ite_eq_right (show (cfgState V (<[id := ()]> L)).cfg.incoming ≠ ∅ from hne)]
  have Hsd : ¬ SymdiffTooBig V V := by
    unfold SymdiffTooBig symdiffN
    rw [GMap.map_difference_diag, GMap.map_size_empty]
    decide
  unfold simpleM
  rw [clearAutoLeave_cfgState, ite_eq_right (fun h => h (cfgInv_cfgState V L Hd)),
    ite_eq_right (fun h => h rfl), Happ]
  simp only
  rw [ite_eq_right (show ¬ SymdiffTooBig (cfgState V L).cfg.incoming
    (cfgState V (<[id := ()]> L)).cfg.incoming from Hsd)]
  simp [checkedM, cfgInv_cfgState _ _ Hd']


/-! ### Changes of the learners only (2026-10-13, stage L part 3)

`CCVoterKeep cfg t ccs`: whatever the learners, the change answers a non-joint configuration
with the same voters and some learners -- an `AddLearnerNode` or a `RemoveNode` of an id that
is not a voter, an `UpdateNode`, or a change with `NodeId = 0`. -/

/-- A change that keeps the voters `cfg`, whatever the learners. -/
def CCVoterKeep (cfg : GSet w64) (t : raftpb.ConfChangeTransition)
    (ccs : List ConfChangeSingleM) : Prop :=
  ∀ lrn : GSet w64, (∀ k, k ∈ lrn → k ∉ cfg) →
    ∃ lrn' : GSet w64, (∀ k, k ∈ lrn' → k ∉ cfg) ∧
      ccApplyM t ccs (cfgState cfg lrn) = some (cfgState cfg lrn')

/-- A change whose model answer is a non-joint configuration with the voters it started from
is a `Simple` one (`ccApplyM_noop`, for any learners on either side). -/
theorem ccApplyM_simple (cfg lrn lrn' : GSet w64) (Hd : ∀ k, k ∈ lrn → k ∉ cfg)
    (t : raftpb.ConfChangeTransition) (ccs : List ConfChangeSingleM)
    (H : ccApplyM t ccs (cfgState cfg lrn) = some (cfgState cfg lrn')) :
    ¬ (t = W32 0 ∧ ccs = []) ∧ (∃ al, enterJointOf t ccs.length = some (al, false)) ∧
      simpleM ccs (cfgState cfg lrn) = some (cfgState cfg lrn') := by
  unfold ccApplyM at H
  by_cases Hl : t = W32 0 ∧ ccs = []
  · rw [ite_eq_left Hl] at H
    unfold leaveJointM at H
    rw [ite_eq_right (fun h => h (cfgInv_cfgState cfg lrn Hd)),
      ite_eq_left (show (cfgState cfg lrn).cfg.outgoing = ∅ from rfl)] at H
    cases H
  rw [ite_eq_right Hl] at H
  refine ⟨Hl, ?_⟩
  rcases He : enterJointOf t ccs.length with _ | ⟨al, ok⟩
  · rw [He] at H; cases H
  rw [He] at H
  cases ok
  · exact ⟨⟨al, rfl⟩, H⟩
  · exfalso
    simp only at H
    unfold enterJointM at H
    rw [ite_eq_right (fun h => h (cfgInv_cfgState cfg lrn Hd)), ite_eq_right (fun h => h rfl)] at H
    by_cases Hin : (cfgState cfg lrn).cfg.incoming = ∅
    · rw [ite_eq_left Hin] at H; cases H
    rw [ite_eq_right Hin] at H
    revert H
    generalize Happ : applyM ccs _ = r
    cases r with
    | none => intro H; cases H
    | some s1 =>
      intro H
      simp only [checkedM] at H
      split at H
      · simp only [Option.some.injEq] at H
        have Hout := applyM_outgoing ccs _ s1 Happ
        have h2 : s1.cfg.outgoing = (cfgState cfg lrn').cfg.outgoing := by rw [← H]
        rw [h2] at Hout
        exact Hin Hout.symm
      · cases H

theorem cfgFlags_delete_learner (V L : GSet w64) (id : w64) (h : id ∉ V) :
    GMap.delete id (cfgFlags V L) = cfgFlags V (GMap.delete id L) := by
  apply GMap.map_eq; intro k
  rw [cfgFlags_lookup]
  by_cases hk : id = k
  · subst hk
    rw [GMap.lookup_delete, ite_eq_right h,
      ite_eq_right (show id ∉ (GMap.delete id L : GSet w64) by
        rw [GMap.elem_of_gset, GMap.lookup_delete]; simp)]
  · rw [GMap.lookup_delete_ne _ hk, cfgFlags_lookup]
    have e : k ∈ (GMap.delete id L : GSet w64) ↔ k ∈ L := by
      rw [GMap.elem_of_gset, GMap.elem_of_gset, GMap.lookup_delete_ne _ hk]
    by_cases h1 : k ∈ V
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : k ∈ L
      · rw [ite_eq_left h2, ite_eq_left (e.2 h2)]
      · rw [ite_eq_right h2, ite_eq_right (fun h' => h2 (e.1 h'))]

/-- `Simple([RemoveNode id])` on `cfgState V L`, `V` non-empty, `id` not a voter: `id` leaves
the learners (nothing if untracked). -/
theorem simpleM_cfgState_removeLearner (V L : GSet w64) (c : ConfChangeSingleM)
    (Hty : c.Type' = W32 1) (h0 : c.NodeId' ≠ W64 0) (hV : c.NodeId' ∉ V) (hne : V ≠ ∅) (Hd : ∀ k, k ∈ L → k ∉ V) :
    simpleM [c] (cfgState V L) = some (cfgState V (GMap.delete c.NodeId' L)) := by
  have Hd' : ∀ k, k ∈ (GMap.delete c.NodeId' L : GSet w64) → k ∉ V := by
    intro k h
    apply Hd k
    rw [GMap.elem_of_gset] at h ⊢
    by_cases hk : c.NodeId' = k
    · subst hk; rw [GMap.lookup_delete] at h; cases h
    · rw [GMap.lookup_delete_ne _ hk] at h; exact h
  have Hrm : removeM c.NodeId' (cfgState V L) = cfgState V (GMap.delete c.NodeId' L) := by
    unfold removeM
    split
    · have hout : c.NodeId' ∉ (cfgState V L).cfg.outgoing := GMap.not_elem_of_empty _
      rw [ite_eq_right hout]
      rw [removeCfg_nw rfl]
      simp only [cfgState, cfgM]
      rw [GMap.delete_notin _ _ (gset_lookup_none V _ hV), GMap.delete_empty,
        cfgFlags_delete_learner V L _ hV]
    · rename_i hn
      have hL : c.NodeId' ∉ L := fun h => hn ((cfgFlags_mem V L _).2 (.inr h))
      rw [GMap.delete_notin _ _ (gset_lookup_none L _ hL)]
  have Happ : applyM [c] (cfgState V L) = some (cfgState V (GMap.delete c.NodeId' L)) := by
    simp only [applyM, applyAll, applyOne, ite_eq_right h0, Hty]
    rw [ite_eq_right (show (W32 1 : w32) ≠ W32 0 by decide),
      ite_eq_right (show (W32 1 : w32) ≠ W32 3 by decide)]
    simp only [ite_true, Option.bind_some]
    rw [Hrm]
    try simp only [Option.bind_some]
    rw [ite_eq_right (show (cfgState V (GMap.delete c.NodeId' L)).cfg.incoming ≠ ∅ from hne)]
  have Hsd : ¬ SymdiffTooBig V V := by
    unfold SymdiffTooBig symdiffN
    rw [GMap.map_difference_diag, GMap.map_size_empty]
    decide
  unfold simpleM
  rw [clearAutoLeave_cfgState, ite_eq_right (fun h => h (cfgInv_cfgState V L Hd)),
    ite_eq_right (fun h => h rfl), Happ]
  simp only
  rw [ite_eq_right (show ¬ SymdiffTooBig (cfgState V L).cfg.incoming
    (cfgState V (GMap.delete c.NodeId' L)).cfg.incoming from Hsd)]
  simp [checkedM, cfgInv_cfgState _ _ Hd']

/-! ### Removing a voter (2026-10-15, stage N: the register's membership change) -/

theorem cfgFlags_delete_voter (V L : GSet w64) (id : w64) (h : id ∉ L) :
    GMap.delete id (cfgFlags V L) = cfgFlags (GMap.delete id V) L := by
  apply GMap.map_eq; intro k
  rw [cfgFlags_lookup]
  by_cases hk : id = k
  · subst hk
    rw [GMap.lookup_delete,
      ite_eq_right (show id ∉ (GMap.delete id V : GSet w64) by
        rw [GMap.elem_of_gset, GMap.lookup_delete]; simp), ite_eq_right h]
  · rw [GMap.lookup_delete_ne _ hk, cfgFlags_lookup]
    have e : k ∈ (GMap.delete id V : GSet w64) ↔ k ∈ V := by
      rw [GMap.elem_of_gset, GMap.elem_of_gset, GMap.lookup_delete_ne _ hk]
    by_cases h1 : k ∈ V
    · rw [ite_eq_left h1, ite_eq_left (e.2 h1)]
    · rw [ite_eq_right h1, ite_eq_right (fun h' => h1 (e.1 h'))]

/-- One voter fewer changes the voters by at most one. -/
theorem not_symdiffTooBig_delete (V : GSet w64) (id : w64) :
    ¬ SymdiffTooBig V (GMap.delete id V) := by
  unfold SymdiffTooBig symdiffN
  have h1 : (GMap.delete id V) \ V = ∅ := by
    apply GMap.map_eq; intro k
    by_cases hk : id = k
    · subst hk; rw [GMap.lookup_sdiff, GMap.lookup_delete]; simp
    · rw [GMap.lookup_sdiff, GMap.lookup_delete_ne _ hk]
      rcases h : V !! k with _ | v <;> simp
  have h2 : GMap.size (V \ (GMap.delete id V)) ≤ 1 := by
    have hsub : V \ (GMap.delete id V) ⊆ ({[id := ()]} : GMap w64 Unit) := by
      intro k v hkv
      by_cases hk : id = k
      · subst hk; cases v; simp
      · rw [GMap.lookup_sdiff, GMap.lookup_delete_ne _ hk] at hkv
        rcases h : V !! k with _ | v' <;> simp_all
    have := GMap.map_subseteq_size hsub
    rw [GMap.map_size_singleton] at this
    exact this
  rw [h1, GMap.map_size_empty]
  generalize GMap.size (V \ (GMap.delete id V)) = n at h2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with h0 | h0 <;> subst h0 <;> decide

/-- `Simple([RemoveNode id])` on `cfgState V L`, `id` a voter (so no learner) whose removal
leaves a voter: `id` leaves the voters. -/
theorem simpleM_cfgState_removeVoter (V L : GSet w64) (c : ConfChangeSingleM)
    (Hty : c.Type' = W32 1) (h0 : c.NodeId' ≠ W64 0) (hV : c.NodeId' ∈ V)
    (hne : (GMap.delete c.NodeId' V : GSet w64) ≠ ∅) (Hd : ∀ k, k ∈ L → k ∉ V) :
    simpleM [c] (cfgState V L) = some (cfgState (GMap.delete c.NodeId' V) L) := by
  have hL : c.NodeId' ∉ L := fun h => Hd _ h hV
  have Hd' : ∀ k, k ∈ L → k ∉ (GMap.delete c.NodeId' V : GSet w64) := by
    intro k hk h
    apply Hd k hk
    rw [GMap.elem_of_gset] at h ⊢
    by_cases hkk : c.NodeId' = k
    · subst hkk; rw [GMap.lookup_delete] at h; cases h
    · rw [GMap.lookup_delete_ne _ hkk] at h; exact h
  have Hrm : removeM c.NodeId' (cfgState V L) = cfgState (GMap.delete c.NodeId' V) L := by
    unfold removeM
    rw [ite_eq_left (show c.NodeId' ∈ (cfgState V L).prs from (cfgFlags_mem V L _).2 (.inl hV))]
    have hout : c.NodeId' ∉ (cfgState V L).cfg.outgoing := GMap.not_elem_of_empty _
    rw [ite_eq_right hout]
    rw [removeCfg_nw rfl]
    simp only [cfgState, cfgM]
    rw [GMap.delete_notin _ _ (gset_lookup_none L _ hL), GMap.delete_empty,
      cfgFlags_delete_voter V L _ hL]
  have Happ : applyM [c] (cfgState V L) = some (cfgState (GMap.delete c.NodeId' V) L) := by
    simp only [applyM, applyAll, applyOne, ite_eq_right h0, Hty]
    rw [ite_eq_right (show (W32 1 : w32) ≠ W32 0 by decide),
      ite_eq_right (show (W32 1 : w32) ≠ W32 3 by decide)]
    simp only [ite_true, Option.bind_some]
    rw [Hrm]
    try simp only [Option.bind_some]
    rw [ite_eq_right (show (cfgState (GMap.delete c.NodeId' V) L).cfg.incoming ≠ ∅ from hne)]
  unfold simpleM
  rw [clearAutoLeave_cfgState, ite_eq_right (fun h => h (cfgInv_cfgState V L Hd)),
    ite_eq_right (fun h => h rfl), Happ]
  simp only
  rw [ite_eq_right (show ¬ SymdiffTooBig (cfgState V L).cfg.incoming
    (cfgState (GMap.delete c.NodeId' V) L).cfg.incoming from not_symdiffTooBig_delete V _)]
  simp [checkedM, cfgInv_cfgState _ _ Hd']

/-- The one `Simple` change of a `ConfChange` (or a one-change `ConfChangeV2` with transition
`Auto`) whose model answer is some learners (`CCVoterKeep`'s witness). -/
theorem ccApplyM_single (cfg lrn lrn' : GSet w64) (c : ConfChangeSingleM)
    (H : simpleM [c] (cfgState cfg lrn) = some (cfgState cfg lrn')) :
    ccApplyM (W32 0) [c] (cfgState cfg lrn) = some (cfgState cfg lrn') := by
  unfold ccApplyM
  rw [ite_eq_right (by simp)]
  have He : enterJointOf (W32 0) [c].length = some (false, false) := by
    simp [enterJointOf]
  rw [He]
  exact H

/-- An `AddLearnerNode` of a non-voter keeps the voters (a no-op for `NodeId = 0`). -/
theorem ccVoterKeep_addLearner (cfg : GSet w64) (Hne : cfg ≠ ∅) (c : ConfChangeSingleM)
    (Hty : c.Type' = W32 3) (Hid : c.NodeId' ∉ cfg) : CCVoterKeep cfg (W32 0) [c] := by
  intro lrn Hd
  by_cases h0 : c.NodeId' = W64 0
  · exact ⟨lrn, Hd, ccApplyM_single_noop cfg lrn Hd c h0 Hne⟩
  have Hc : c = addLearnerCC c.NodeId' := by cases c; simp only at Hty; subst Hty; rfl
  refine ⟨<[c.NodeId' := ()]> lrn, ?_, ccApplyM_single cfg lrn _ c ?_⟩
  · intro k hk
    rcases (gset_mem_insert lrn c.NodeId' k).1 hk with h | h
    · subst h; exact Hid
    · exact Hd k h
  · rw [Hc]; exact simpleM_cfgState_addLearner cfg lrn _ h0 Hid Hne Hd

/-- A `RemoveNode` of a non-voter keeps the voters (a no-op for `NodeId = 0` or an untracked
id). -/
theorem ccVoterKeep_removeLearner (cfg : GSet w64) (Hne : cfg ≠ ∅) (c : ConfChangeSingleM)
    (Hty : c.Type' = W32 1) (Hid : c.NodeId' ∉ cfg) : CCVoterKeep cfg (W32 0) [c] := by
  intro lrn Hd
  by_cases h0 : c.NodeId' = W64 0
  · exact ⟨lrn, Hd, ccApplyM_single_noop cfg lrn Hd c h0 Hne⟩
  refine ⟨GMap.delete c.NodeId' lrn, ?_, ccApplyM_single cfg lrn _ c
    (simpleM_cfgState_removeLearner cfg lrn c Hty h0 Hid Hne Hd)⟩
  intro k hk
  apply Hd k
  rw [GMap.elem_of_gset] at hk ⊢
  by_cases hkk : c.NodeId' = k
  · subst hkk; rw [GMap.lookup_delete] at hk; cases hk
  · rw [GMap.lookup_delete_ne _ hkk] at hk; exact hk


/-- A change that keeps the voters `cfg` and only drops learners, whatever the learners: the
scope of `RawNode.ApplyConfChange` (2026-10-13; until then `CCNoop`). Adding a learner is
outside it only for the bound on the tracked ids (`ownTracker`'s `Hcfg_size`), which a
`RawNode` client cannot state without the learner set. -/
def CCShrink (cfg : GSet w64) (t : raftpb.ConfChangeTransition)
    (ccs : List ConfChangeSingleM) : Prop :=
  ∀ lrn : GSet w64, (∀ k, k ∈ lrn → k ∉ cfg) →
    ∃ lrn' : GSet w64, lrn' ⊆ lrn ∧
      ccApplyM t ccs (cfgState cfg lrn) = some (cfgState cfg lrn')

theorem CCNoop.shrink {cfg : GSet w64} {t : raftpb.ConfChangeTransition}
    {ccs : List ConfChangeSingleM} (H : CCNoop cfg t ccs) : CCShrink cfg t ccs :=
  fun lrn Hd => ⟨lrn, GMap.subseteq_refl _, H lrn Hd⟩

/-- A `RemoveNode` of a non-voter only drops learners. -/
theorem ccShrink_removeLearner (cfg : GSet w64) (Hne : cfg ≠ ∅) (c : ConfChangeSingleM)
    (Hty : c.Type' = W32 1) (Hid : c.NodeId' ∉ cfg) : CCShrink cfg (W32 0) [c] := by
  intro lrn Hd
  by_cases h0 : c.NodeId' = W64 0
  · exact ⟨lrn, GMap.subseteq_refl _, ccApplyM_single_noop cfg lrn Hd c h0 Hne⟩
  refine ⟨GMap.delete c.NodeId' lrn, GMap.delete_subseteq _ _, ccApplyM_single cfg lrn _ c
    (simpleM_cfgState_removeLearner cfg lrn c Hty h0 Hid Hne Hd)⟩

/-- The premise `raft.applyConfChange` takes, from a `CCShrink` change on a node tracking
`domSet prs`: the new learners are among the old ones, so the bound on the tracked ids holds. -/
theorem applyCC_of_shrink (cfg : GSet w64) {V : Type} (prs : GMap w64 V)
    (t : raftpb.ConfChangeTransition) (ccs : List ConfChangeSingleM)
    (H : CCShrink cfg t ccs) (Hsub : cfg ⊆ domSet prs) (Hsz : (GMap.size prs : Int) ≤ 2 ^ 62) :
    ∃ lrn', (∀ k, k ∈ lrn' → k ∉ cfg) ∧ (GMap.size (cfg ∪ lrn') : Int) ≤ 2 ^ 62 ∧
      ccApplyM t ccs (cfgState cfg (domSet prs \ cfg)) = some (cfgState cfg lrn') ∧
      -- (D19p, 2026-10-18) the learners only shrink
      (∀ k, k ∈ lrn' → k ∈ domSet prs) := by
  obtain ⟨lrn', Hl, Hm⟩ := H (domSet prs \ cfg) (fun k hk => ((GMap.elem_of_difference _ _ _).1 hk).2)
  refine ⟨lrn', fun k hk => ((GMap.elem_of_difference _ _ _).1
    ((GMap.elem_of_subseteq _ _).1 Hl k hk)).2, ?_, Hm,
    fun k hk => ((GMap.elem_of_difference _ _ _).1 ((GMap.elem_of_subseteq _ _).1 Hl k hk)).1⟩
  have h1 : cfg ∪ lrn' ⊆ domSet prs := by
    rw [GMap.union_subseteq]
    refine ⟨Hsub, ?_⟩
    rw [GMap.elem_of_subseteq]; intro k hk
    exact ((GMap.elem_of_difference _ _ _).1 ((GMap.elem_of_subseteq _ _).1 Hl k hk)).1
  have h2 := GMap.subseteq_size h1
  rw [GMap.size_dom] at h2
  omega

end model

end EtcdGrove
end Perennial
