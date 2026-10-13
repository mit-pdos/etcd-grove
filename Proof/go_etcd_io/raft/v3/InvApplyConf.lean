/-
Applying a configuration change (`raft.applyConfChange`, `RawNode.ApplyConfChange`),
Lean-first (2026-10-13, reconfiguration stage D): changes that leave the configuration
unchanged.

* The model of `applyConfChange`'s choice (`ccApplyM`: `LeaveJoint`, `EnterJoint` or
  `Simple`, on the `ConfChangeV2` that `AsV2` makes of the change, `ccV2Of`), and the state
  `confchange` sees of the node's configuration (`cfgState cfg`: the voters `cfg`, nothing
  else, every tracked `Progress` a non-learner). The scope of these specs is a change whose
  model answer is that same state (`ccApplyM ... (cfgState cfg) = some (cfgState cfg)`); only
  `Simple` can answer that (`ccApplyM_noop`), e.g. for a change with `NodeId = 0`, which
  `Changer.apply` skips (`ccApplyM_single_noop`).
* `ownTracker_toCC`: the node's tracker as the `Changer` reads it (`ownTrackerCC`), the old
  `Progress` objects' inflight rings set apart (`progRAt`).
* `ownResult_noop_transfer`: `Simple`'s result, with the rings moved to the new `Progress`
  objects (copies, or fresh ones), as `switchToConfig` takes it (`ownConfigV`), each new
  `Match` the old one or `0` (`MatchKept`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.InvConfchange
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg

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

/-- The configuration with voters `cfg` and learners `lrn` as a `Config`. -/
def cfgM (cfg lrn : GSet w64) : CfgM :=
  { incoming := cfg, outgoing := ∅, learners := lrn, learnersNext := ∅, autoLeave := false }

/-- What `confchange` sees of a node whose configuration is `cfg` with the learners `lrn`
(`ownTracker`: `lrn` is the tracked ids outside `cfg`). -/
def cfgState (cfg lrn : GSet w64) : CCState := { cfg := cfgM cfg lrn, prs := cfgFlags cfg lrn }

/-- What `ConfChangeI.AsV2()` makes of a change: a `ConfChange` is one change with
transition `Auto` (`ConfChange.AsV2`'s spec); a `ConfChangeV2` is itself. -/
def ccV2Of : CCMsg → raftpb.ConfChangeTransition × List raftpb.ConfChangeSingle
  | .v1 m => (W32 0, [{ Type' := m.type, NodeId' := m.nodeId }])
  | .v2 m => (m.transition, m.changes)

/-- `raft.applyConfChange`'s choice (raft.go): `LeaveJoint` for an empty `Auto` change,
else `EnterJoint` when `ConfChangeV2.EnterJoint` says so, else `Simple`; `none` where
`EnterJoint` panics (an undefined transition with joint consensus). -/
def ccApplyM (t : raftpb.ConfChangeTransition) (ccs : List raftpb.ConfChangeSingle)
    (s : CCState) : Option CCState :=
  if t = W32 0 ∧ ccs = [] then leaveJointM s
  else match enterJointOf t ccs.length with
    | some (al, true) => enterJointM al ccs s
    | some (_, false) => simpleM ccs s
    | none => none

/-- A change that leaves every configuration with the voters `cfg` as it is, whatever its
learners (2026-10-13): the scope of `RawNode.ApplyConfChange`, whose state does not say
which learners the node tracks. -/
def CCNoop (cfg : GSet w64) (t : raftpb.ConfChangeTransition)
    (ccs : List raftpb.ConfChangeSingle) : Prop :=
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
    rw [cfgFlags_lookup, if_neg (Hd k hk), if_pos (show k ∈ lrn from hk)]

theorem clearAutoLeave_cfgState (cfg lrn : GSet w64) :
    clearAutoLeave (cfgState cfg lrn) = cfgState cfg lrn := rfl

theorem applyOne_outgoing (c : raftpb.ConfChangeSingle) (s s' : CCState)
    (h : applyOne c s = some s') : s'.cfg.outgoing = s.cfg.outgoing := by
  unfold applyOne at h
  by_cases h0 : c.NodeId' = W64 0
  · rw [if_pos h0] at h; cases h; rfl
  rw [if_neg h0] at h
  by_cases h1 : c.Type' = W32 0
  · rw [if_pos h1] at h; cases h
    unfold makeVoterM; split
    · rfl
    · simp [initProgressM]
  rw [if_neg h1] at h
  by_cases h3 : c.Type' = W32 3
  · rw [if_pos h3] at h; cases h
    unfold makeLearnerM
    split
    · simp [initProgressM]
    · rfl
    · split <;> rfl
  rw [if_neg h3] at h
  by_cases h4 : c.Type' = W32 1
  · rw [if_pos h4] at h; cases h
    unfold removeM; split <;> rfl
  rw [if_neg h4] at h
  by_cases h2 : c.Type' = W32 2
  · rw [if_pos h2] at h; cases h; rfl
  rw [if_neg h2] at h
  cases h

theorem applyAll_outgoing (ccs : List raftpb.ConfChangeSingle) (s s' : CCState)
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

theorem applyM_outgoing (ccs : List raftpb.ConfChangeSingle) (s s' : CCState)
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
    (t : raftpb.ConfChangeTransition) (ccs : List raftpb.ConfChangeSingle)
    (H : ccApplyM t ccs (cfgState cfg lrn) = some (cfgState cfg lrn)) :
    ¬ (t = W32 0 ∧ ccs = []) ∧ (∃ al, enterJointOf t ccs.length = some (al, false)) ∧
      simpleM ccs (cfgState cfg lrn) = some (cfgState cfg lrn) := by
  unfold ccApplyM at H
  by_cases Hl : t = W32 0 ∧ ccs = []
  · rw [if_pos Hl] at H
    unfold leaveJointM at H
    rw [if_neg (fun h => h (cfgInv_cfgState cfg lrn Hd)),
      if_pos (show (cfgState cfg lrn).cfg.outgoing = ∅ from rfl)] at H
    cases H
  rw [if_neg Hl] at H
  refine ⟨Hl, ?_⟩
  rcases He : enterJointOf t ccs.length with _ | ⟨al, ok⟩
  · rw [He] at H; cases H
  rw [He] at H
  cases ok
  · exact ⟨⟨al, rfl⟩, H⟩
  · exfalso
    simp only at H
    unfold enterJointM at H
    rw [if_neg (fun h => h (cfgInv_cfgState cfg lrn Hd)), if_neg (fun h => h rfl)] at H
    by_cases Hin : (cfgState cfg lrn).cfg.incoming = ∅
    · rw [if_pos Hin] at H; cases H
    rw [if_neg Hin] at H
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
    (c : raftpb.ConfChangeSingle) (Hc : c.NodeId' = W64 0) (Hne : cfg ≠ ∅) :
    ccApplyM (W32 0) [c] (cfgState cfg lrn) = some (cfgState cfg lrn) := by
  have Happ : applyM [c] (cfgState cfg lrn) = some (cfgState cfg lrn) := by
    simp only [applyM, applyAll, applyOne, Hc, ↓reduceIte, Option.bind_some]
    rw [if_neg (by exact Hne)]
  have Hsd : ¬ SymdiffTooBig cfg cfg := by
    unfold SymdiffTooBig symdiffN
    rw [GMap.map_difference_diag, GMap.map_size_empty]
    decide
  have Hs : simpleM [c] (cfgState cfg lrn) = some (cfgState cfg lrn) := by
    unfold simpleM
    rw [clearAutoLeave_cfgState, if_neg (fun h => h (cfgInv_cfgState cfg lrn Hd)),
      if_neg (fun h => h rfl), Happ]
    simp only
    rw [if_neg (show ¬ SymdiffTooBig (cfgState cfg lrn).cfg.incoming
      (cfgState cfg lrn).cfg.incoming from Hsd)]
    simp [checkedM, cfgInv_cfgState cfg lrn Hd]
  unfold ccApplyM
  rw [if_neg (by simp)]
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
    rw [GMap.lookup_insert_eq, if_pos ((GMap.elem_of_gset _ _).2 (GMap.lookup_insert_eq _ _ _))]
  · rw [GMap.lookup_insert_ne _ _ hk, cfgFlags_lookup]
    have e : k ∈ (<[id := ()]> V : GSet w64) ↔ k ∈ V := by
      rw [GMap.elem_of_gset, GMap.elem_of_gset, GMap.lookup_insert_ne _ _ hk]
    by_cases h1 : k ∈ V
    · rw [if_pos h1, if_pos (e.2 h1)]
    · rw [if_neg h1, if_neg (fun h' => h1 (e.1 h'))]

theorem cfgFlags_insert_learner (V L : GSet w64) (id : w64) (h : id ∉ V) :
    <[id := true]> (cfgFlags V L) = cfgFlags V (<[id := ()]> L) := by
  apply GMap.map_eq; intro k
  rw [cfgFlags_lookup]
  by_cases hk : id = k
  · subst hk
    rw [GMap.lookup_insert_eq, if_neg h,
      if_pos ((GMap.elem_of_gset _ _).2 (GMap.lookup_insert_eq _ _ _))]
  · rw [GMap.lookup_insert_ne _ _ hk, cfgFlags_lookup]
    have e : k ∈ (<[id := ()]> L : GSet w64) ↔ k ∈ L := by
      rw [GMap.elem_of_gset, GMap.elem_of_gset, GMap.lookup_insert_ne _ _ hk]
    by_cases h1 : k ∈ V
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : k ∈ L
      · rw [if_pos h2, if_pos (e.2 h2)]
      · rw [if_neg h2, if_neg (fun h' => h2 (e.1 h'))]

theorem gset_lookup_none (L : GSet w64) (id : w64) (h : id ∉ L) : L !! id = none := by
  cases hl : L !! id with
  | none => rfl
  | some u => exact absurd ((GMap.elem_of_gset _ _).2 (by cases u; exact hl)) h

theorem gset_insert_ne_empty (V : GSet w64) (id : w64) : (<[id := ()]> V : GSet w64) ≠ ∅ := by
  intro h; have := congrArg (fun m => m !! id) h; simp at this

theorem gset_mem_insert (V : GSet w64) (id k : w64) :
    k ∈ (<[id := ()]> V : GSet w64) ↔ k = id ∨ k ∈ V := by
  rw [GMap.elem_of_gset, GMap.elem_of_gset]
  by_cases hk : id = k
  · subst hk; simp
  · rw [GMap.lookup_insert_ne _ _ hk]; simp [Ne.symm hk]

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
    simp only [applyM, applyAll, applyOne, if_neg hid', ↓reduceIte, Option.bind_some]
    rw [Hmv]
    try simp only [Option.bind_some]
    rw [if_neg (show (cfgState (<[id := ()]> V) L).cfg.incoming ≠ ∅ from
      gset_insert_ne_empty V id)]
  unfold simpleM
  rw [clearAutoLeave_cfgState, if_neg (fun h => h (cfgInv_cfgState V L Hd)),
    if_neg (fun h => h rfl), Happ]
  simp only
  rw [if_neg (show ¬ SymdiffTooBig (cfgState V L).cfg.incoming
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
    rw [if_neg hV] at hlk
    by_cases hl : id ∈ L
    · rw [if_pos hl] at hlk
      simp only [cfgState] at hlk ⊢
      rw [hlk]
      simp only
      rw [GMap.insert_id L id () ((GMap.elem_of_gset _ _).1 hl)]
    · rw [if_neg hl] at hlk
      simp only [cfgState] at hlk ⊢
      rw [hlk]
      simp only [initProgressM, cfgM, ↓reduceIte]
      rw [cfgFlags_insert_learner V L id hV]
  have Happ : applyM [addLearnerCC id] (cfgState V L) = some (cfgState V (<[id := ()]> L)) := by
    have hid' : (addLearnerCC id).NodeId' ≠ W64 0 := hid
    simp only [applyM, applyAll, applyOne, if_neg hid', ↓reduceIte, Option.bind_some]
    rw [Hml, if_neg (show (W32 3 : w32) ≠ W32 0 by decide)]
    simp only [Option.bind_some]
    rw [if_neg (show (cfgState V (<[id := ()]> L)).cfg.incoming ≠ ∅ from hne)]
  have Hsd : ¬ SymdiffTooBig V V := by
    unfold SymdiffTooBig symdiffN
    rw [GMap.map_difference_diag, GMap.map_size_empty]
    decide
  unfold simpleM
  rw [clearAutoLeave_cfgState, if_neg (fun h => h (cfgInv_cfgState V L Hd)),
    if_neg (fun h => h rfl), Happ]
  simp only
  rw [if_neg (show ¬ SymdiffTooBig (cfgState V L).cfg.incoming
    (cfgState V (<[id := ()]> L)).cfg.incoming from Hsd)]
  simp [checkedM, cfgInv_cfgState _ _ Hd']

end model

/-! ## The tracker as a `Changer` reads it, and the result as `switchToConfig` takes it -/

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `ownProgress pr p` holds besides the points-to, for the record `peers` holds at `k`:
the inflight ring and that the value is a non-learner `Progress` of the record. -/
def progRAt (peers : GMap w64 Progress) (k : w64) (pv : tracker.Progress) : IProp GF :=
  iprop(∃ p, ⌜peers !! k = some p⌝ ∗ ownInflights pv.Inflights' p.infl ∗
    ⌜progressAbs pv p.infl = some p⌝)

/-- A set is its own domain. -/
theorem domSet_gset (s : GSet w64) : domSet s = s := by
  apply GMap.map_eq; intro k
  simp only [domSet, GMap.lookup_fmap]
  cases s !! k <;> rfl

/-- The node's tracker as the `Changer` reads it: the configuration `cfgM cfg lrn` (`lrn` the
learners, the tracked ids outside `cfg`), the progress map (read-only) and the `Progress`
objects with their values `pvs`; the inflight rings set apart, and the tally. The old
objects and voter map are garbage once `switchToConfig` has installed the new ones; their
rings go to the copies (`ownResult_noop_transfer`). -/
theorem ownTracker_toCC (cfg : GSet w64) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTracker (GF := GF) cfg tv t ⊢ ∃ (pvs : GMap w64 tracker.Progress),
      ownTrackerCC tv (DFrac.own 1) DFrac.discard (DFrac.own 1)
        (cfgM cfg (domSet t.prs \ cfg)) t.prs pvs ∗
      ([∗map] k ↦ pv ∈ pvs, progRAt t.peers k pv) ∗
      tv.Votes' ↦$ t.votes ∗
      ⌜flagsOf pvs = cfgFlags cfg (domSet t.prs \ cfg)⌝ ∗
      ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
      ⌜cfg ⊆ domSet t.prs ∧ (GMap.size t.prs : Int) ≤ 2 ^ 62⌝ := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  obtain ⟨Hldom, Hlnx, Hfl⟩ := Hno_learners
  subst Hlnx
  have Hlrn : learners = domSet t.prs \ cfg := by rw [← Hldom, domSet_gset]
  -- the values of the `Progress` objects, and their rings apart
  ihave H : ([∗map] k ↦ pr;p ∈ t.prs;t.peers, ∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = decide (k ∉ cfg)⌝ ∗ (emp ∗ progRAt (GF := GF) t.peers k pv)) :
        IProp GF))
      $$ [Hprogs]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr p} _ hp => ?_)) $$ Hprogs
    iintro Hp
    unfold ownProgress
    iNamed Hp
    iexists pv
    iframe Hpv
    isplitr
    · ipureintro; exact ((progressAbs_Some _ _ _).1 Habs).1.trans (Hfl k p hp)
    isplitr
    · iempintro
    unfold progRAt
    iexists p
    iframe Hinfl
    ipureintro; exact ⟨hp, Habs⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ H
  have Hdom0' : ∀ k, (t.prs !! k).isSome ↔ (t.peers !! k).isSome := Hdom0
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr => iprop(∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = decide (k ∉ cfg)⌝ ∗ (emp ∗ progRAt (GF := GF) t.peers k pv)) :
        IProp GF)))
    (Φ2 := fun (_ : w64) (_ : Progress) => (emp : IProp GF)) Hdom0).1 $$ [H] with ⟨H, -⟩
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr p} _ _ => ?_)) $$ H
    iintro H; iframe H
  icases bigSepM_exist_sepM2 t.prs _ $$ H with ⟨%pvs, H⟩
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ H
  have Hdom' : ∀ k, (t.prs !! k).isSome ↔ (pvs !! k).isSome := Hdom
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hpt, H⟩
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hl, H⟩
  ihave %Hlf := BigSepM2.bigSepM2_pure_intro $$ Hl
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun k pv => progRAt (GF := GF) t.peers k pv) Hdom).1 $$ H with ⟨-, HR⟩
  iexists pvs
  iframe HR Hvotes
  isplitl [Hvoters Hpt Hlearners HlearnersNext]
  · unfold ownTrackerCC
    iframe Hpt
    isplitl [Hvoters Hlearners HlearnersNext]
    · have Hv : voters = cfg := by rw [← Hvoters_dom, domSet_gset]
      subst Hv
      subst Hlrn
      iapply ownCfgCC_intro tv.Config' (DFrac.own 1) (cfgM voters (domSet t.prs \ voters))
        voters_ref map.nil Hvoters_arr Hautoleave $$ [Hvoters] [] [Hlearners] [HlearnersNext]
      · simp only [cfgM]; iexact Hvoters
      · simp only [cfgM]; iapply ownIdsetC_nil
      · simp only [cfgM]; iexact Hlearners
      · simp only [cfgM]; iexact HlearnersNext
    · iexact Hprs
  ipureintro
  refine ⟨?_, HmaxInfl, Hprs_dom, Hcfg_size⟩
  apply GMap.map_eq; intro k
  rw [flagsOf_lookup', cfgFlags_lookup]
  cases hpv : pvs !! k with
  | none =>
    have hk : k ∉ domSet t.prs := by
      rw [GMap.elem_of_dom']
      intro h
      have := (Hdom' k).1 h
      rw [hpv] at this; cases this
    have hc : k ∉ cfg := fun h => hk ((GMap.elem_of_subseteq _ _).1 Hprs_dom _ h)
    have hl : k ∉ domSet t.prs \ cfg := fun h => hk ((GMap.elem_of_difference _ _ _).1 h).1
    simp [hc, hl]
  | some pv =>
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom' k).2 (by rw [hpv]; rfl))
    have Hl0 := Hlf k pr pv hpr hpv
    have hk : k ∈ domSet t.prs := (GMap.elem_of_dom _ _).2 ⟨pr, hpr⟩
    simp only [Option.map_some]
    rw [Hl0]
    by_cases hc : k ∈ cfg
    · simp [hc]
    · have hl : k ∈ domSet t.prs \ cfg := (GMap.elem_of_difference _ _ _).2 ⟨hk, hc⟩
      simp [hc, hl]

/-- What `Simple`'s result is, once the old objects' rings are moved to it: each new object
an `ownProgress` (`Q`), its record the old one or one with `Match = 0`. -/
private def newPrQ (peers : GMap w64 Progress) (k : w64) (pv : tracker.Progress) : IProp GF :=
  iprop(∃ p, ownInflights pv.Inflights' p.infl ∗
    ⌜progressAbs pv p.infl = some p ∧
      (uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched)⌝)

/-- `Simple`'s result for an unchanged configuration (`cfgState cfg lrn`), with the old
objects' inflight rings moved to the new ones (`ownNewPr_transfer`): the configuration and
progress map `switchToConfig` takes (`ownConfigV`, the progress map made read-only), each new
`Match` the old one or `0` (`MatchKept`). -/
theorem ownResult_noop_transfer (cfg lrn : GSet w64) (Hd : ∀ k, k ∈ lrn → k ∉ cfg)
    (chg : confchange.Changer)
    (base : GMap w64 tracker.Progress) (peers : GMap w64 Progress) (cfgv : tracker.Config)
    (trk : Loc) (Hsz : (GMap.size (cfg ∪ lrn) : Int) ≤ 2 ^ 62) :
    ownCfgCC (GF := GF) cfgv (DFrac.own 1) (cfgM cfg lrn) ∗
      ownPrsW chg base trk (cfgFlags cfg lrn) ∗
      ([∗map] k ↦ pv ∈ base, progRAt peers k pv) ⊢
      |==> ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
        ownConfigV cfg cfgv trk prs pvs ∗ ⌜MatchKept peers pvs⌝ ∗
        ⌜domSet prs = cfg ∪ lrn⌝ := by
  iintro ⟨Hc, Hw, HR⟩
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
  icases ownIdsetC_nil_of _ _ (cfgM cfg lrn).outgoing rfl $$ Hout with %Hvout
  icases ownIdsetC_nil_of _ _ (cfgM cfg lrn).learnersNext rfl $$ Hln with %Hln
  subst Hvout
  unfold ownPrsW
  icases Hw with ⟨%prs, %pvs, Htrk, Hprs, %Hflags, Hnew⟩
  -- the rings, to the new objects
  ihave HQ := ownNewPr_transfer chg base (fun k pv => progRAt (GF := GF) peers k pv)
      (fun k pv => newPrQ (GF := GF) peers k pv) ?_ ?_ pvs $$ [$HR $Hnew]
  · -- a copy (`IsLearner` possibly changed)
    intro k pv0 pv _ h1
    unfold progRAt newPrQ
    iintro ⟨%p, %Hp, Hinfl, %Habs⟩
    iexists { p with learner := pv.IsLearner' }
    have Hinf : pv.Inflights' = pv0.Inflights' := by rw [h1]
    rw [Hinf]
    iframe Hinfl
    ipureintro
    obtain ⟨_, h2, h3, h4, h5, h6, h7, h8⟩ := (progressAbs_Some _ _ _).1 Habs
    refine ⟨(progressAbs_Some _ _ _).2 ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, h8⟩, .inr ⟨p, Hp, rfl⟩⟩ <;>
      (rw [h1]; assumption)
  · -- a fresh one
    intro k pv Hf
    unfold newPrQ
    iintro Hinfl
    iexists progressOf pv .probe (inflightsNew chg.Tracker'.MaxInflight'
      chg.Tracker'.MaxInflightBytes')
    isplitl [Hinfl]
    · simp only [progressOf]; iexact Hinfl
    ipureintro
    obtain ⟨Hm, -, -, Hst, -, -, -⟩ := Hf
    refine ⟨(progressAbs_Some _ _ _).2 ⟨rfl, Hst, rfl, rfl, rfl, rfl, rfl, rfl⟩, .inl ?_⟩
    simp only [progressOf, Hm]; rfl
  -- each new object a learner exactly outside `cfg`, the domain `cfg ∪ lrn`
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  have Hlf : ∀ k pv, pvs !! k = some pv → pv.IsLearner' = decide (k ∉ cfg) := by
    intro k pv h
    have h' := flagsOf_lookup pvs k pv h
    rw [Hflags, cfgFlags_lookup] at h'
    by_cases hc : k ∈ cfg
    · rw [if_pos hc] at h'; rw [← Option.some.inj h']; simp [hc]
    · rw [if_neg hc] at h'
      by_cases hl : k ∈ lrn
      · rw [if_pos hl] at h'; rw [← Option.some.inj h']; simp [hc]
      · rw [if_neg hl] at h'; cases h'
  have Hpdom : domSet prs = cfg ∪ lrn := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom', GMap.mem_iff, Hdom k, ← flagsOf_mem, Hflags, cfgFlags_mem,
      GMap.elem_of_union]
  -- the objects, as `ownProgress`es with their records
  ihave HQ2 := (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun k pv => newPrQ (GF := GF) peers k pv) (m1 := prs) (m2 := pvs) Hdom0).2 $$ [HQ]
  · isplitr
    · iapply (BigSepM.bigSepM_emp (m := prs)).2
      iempintro
    · iexact HQ
  ihave H := BigSepM2.bigSepM2_sep_eqv.2 $$ [$Hprs $HQ2]
  ihave H : ([∗map] k ↦ pr;pv ∈ prs;pvs, ((∃ p, ownProgress pr p ∗
      ⌜(uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched) ∧
        p.learner = decide (k ∉ cfg)⌝) ∗ emp :
        IProp GF)) $$ [H]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr pv} _ hpv => ?_)) $$ H
    iintro ⟨Hp, -, HQ⟩
    unfold newPrQ
    icases HQ with ⟨%p, Hinfl, %Hp⟩
    obtain ⟨Habs, Hm⟩ := Hp
    isplitl
    · iexists p
      isplitl
      · iapply ownProgress_intro _ _ p $$ Hp Hinfl
        ipureintro; exact Habs
      · ipureintro
        exact ⟨Hm, ((progressAbs_Some _ _ _).1 Habs).1.symm.trans (Hlf k pv hpv)⟩
    · iempintro
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr => iprop(∃ p, ownProgress (GF := GF) pr p ∗
      ⌜(uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched) ∧
        p.learner = decide (k ∉ cfg)⌝))
    (Φ2 := fun (_ : w64) (_ : tracker.Progress) => (emp : IProp GF)) (m1 := prs) (m2 := pvs)
    Hdom0).1 $$ H with ⟨H, -⟩
  icases bigSepM_exist_sepM2 prs _ $$ H with ⟨%ps, H⟩
  ihave %Hdom2 := BigSepM2.bigSepM2_lookup_iff $$ H
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hprogs, Hmk⟩
  ihave %Hmk := BigSepM2.bigSepM2_pure_intro $$ Hmk
  ihave Hin := (show (vin ↦$ (cfgM cfg lrn).incoming : IProp GF) ⊢ vin ↦$ cfg from .rfl) $$ Hin
  ihave Hl := (show ownIdsetC (GF := GF) cfgv.Learners' (DFrac.own 1) (cfgM cfg lrn).learners ⊢
    ownIdsetC cfgv.Learners' (DFrac.own 1) lrn from .rfl) $$ Hl
  have Hdom2' : ∀ k, (prs !! k).isSome ↔ (ps !! k).isSome := Hdom2
  imod ownMap_persist $$ Htrk with #Htrk
  imodintro
  iexists prs, ps
  isplitl
  · unfold ownConfigV
    iexists vin, cfg, lrn
    simp only [named]
    iframe Hin Htrk Hprogs Hl
    ipureintro
    refine ⟨Harr, Hln, Hal, domSet_gset cfg, ?_, ⟨?_, rfl, ?_⟩, ?_⟩
    · rw [Hpdom]; exact GMap.union_subseteq_l _ _
    · apply GMap.set_eq; intro k
      rw [domSet_gset, Hpdom, GMap.elem_of_difference, GMap.elem_of_union]
      constructor
      · intro h; exact ⟨.inr h, Hd k h⟩
      · rintro ⟨h | h, h'⟩
        · exact absurd h h'
        · exact h
    · intro k p hp
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp]; rfl))
      exact (Hmk k pr p hpr hp).2
    · rw [← GMap.size_dom, Hpdom]; exact Hsz
  · ipureintro
    refine ⟨?_, Hpdom⟩
    intro k p' hp'
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp']; rfl))
    exact (Hmk k pr p' hpr hp').1

end heap

end EtcdGrove
end Perennial
