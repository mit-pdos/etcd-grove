/-
The `confchange` package: the pure model of a configuration change, its representation,
and the shared vocabulary of `Spec/go_etcd_io/raft/v3/confchange/*.lean` and
`Spec/go_etcd_io/raft/v3/tracker/Config__Clone.lean`.

Until 2026-10-08 `confchange` was not translated and `confchange.Restore`'s triple was an
`axiom`. It was then translated in full and `Restore` proved, its callees specified only on
`Restore`'s path (a voters-only `ConfState` onto the empty tracker). On 2026-10-12 every
function of the package was specified for all inputs, against a pure model (below):
`Simple`, `EnterJoint`, `LeaveJoint` and their callees, joint configurations, learners,
staged learners, removal and `AutoLeave`, every error path. `Restore`'s statement is
unchanged; its proof derives the old statement of `Simple` from the general one
(`Simple_votersOnly`, `Proof/.../confchange/Restore.lean`). There is no Rocq counterpart:
these files are Lean-first.

* The model: `CfgM` (a `tracker.Config`: incoming and outgoing voters, learners, staged
  learners, `AutoLeave`), `CCState` (with each tracked id's `IsLearner`), `CfgInv` (what
  `checkInvariants` accepts), and one function per `Changer` method (`simpleM`,
  `enterJointM`, `leaveJointM`, `applyM`, `makeVoterM`, `makeLearnerM`, `removeM`, ...),
  `none` on each error.
* The representation: `ownCfgCC` (a `Config` value: the incoming map owned, the other three
  canonical id sets), `ownTrackerCC` (the tracker a `Changer` reads), `ownPrsW`/`ownNewPr`
  (a result's progress map: each `Progress` a copy of the tracker's with `IsLearner`
  changed, or a fresh one with its fresh `Inflights`), `ownResult` (what a method returns
  for the model's answer); `ownNewPr_transfer` moves resources held for the tracker's
  `Progress` objects (their inflight rings) to the copies.
* `ConfigSimple`, `addNodeCC`, `opSpec`: the vocabulary of `Restore` and `chain`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTracker
public import RaftWitness.Proof.go_etcd_io.raft.v3.Protocol.StepC
public import Perennial.Std.ListBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The pure model of a configuration change

What `confchange`'s `Changer` computes, as pure functions on an abstract configuration
(added 2026-10-12, when the package's specs were generalized from the one case `Restore`
reaches to all inputs). A `tracker.Config` is `CfgM`: the incoming and outgoing voter
sets (`Voters[0]`, `Voters[1]`), the learners, the staged learners (`LearnersNext`) and
`AutoLeave`. The progress map is seen only through each tracked id's `IsLearner` flag:
`confchange` reads and writes no other field of a `Progress` (`CCState.prs`). The Go
code's checks are the model's: `CfgInv` is exactly what `checkInvariants` accepts, and
each `Changer` method is an `Option CCState`, `none` on every error path. -/

-- `CfgM`, a `tracker.Config` abstractly, is in `Protocol/StepC.lean` (moved 2026-10-13, so
-- that the protocol's joint-configuration step relation can name it).

/-- Membership in a set with one more id (moved here from `CCApply.lean`, 2026-10-20). -/
theorem gset_mem_insert (V : GSet w64) (id k : w64) :
    k ∈ (<[id := ()]> V : GSet w64) ↔ k = id ∨ k ∈ V := by
  rw [GMap.elem_of_gset, GMap.elem_of_gset]
  by_cases hk : id = k
  · subst hk; simp
  · rw [GMap.lookup_insert_ne _ _ hk]; simp [Ne.symm hk]

/-- A (`Config`, progress map) pair: the configuration, and each tracked id (the progress
map's domain) with its `Progress`'s `IsLearner`. -/
structure CCState where
  cfg : CfgM
  prs : GMap w64 Bool

section model
open Classical
variable [GooseExts]

/-- What `checkInvariants` accepts (confchange.go, `checkInvariants`), check by check:
every voter (incoming or outgoing), learner and staged learner is tracked; a staged learner
is an outgoing voter not marked a learner; a learner is no voter and is marked one; a
non-joint configuration (no outgoing voter) has no staged learner and `AutoLeave` off.
(The Go code also asks that a non-joint config's `Voters[1]` and `LearnersNext` be `nil`,
not merely empty; `ownCfgCC` represents both canonically, `nil` exactly when empty, so
that check is this one.) -/
def CfgInv (s : CCState) : Prop :=
  (∀ id, id ∈ s.cfg.incoming ∨ id ∈ s.cfg.outgoing ∨ id ∈ s.cfg.learners ∨
      id ∈ s.cfg.learnersNext → id ∈ s.prs) ∧
  (∀ id, id ∈ s.cfg.learnersNext → id ∈ s.cfg.outgoing ∧ s.prs !! id = some false) ∧
  (∀ id, id ∈ s.cfg.learners →
      id ∉ s.cfg.outgoing ∧ id ∉ s.cfg.incoming ∧ s.prs !! id = some true) ∧
  (s.cfg.outgoing = ∅ → s.cfg.learnersNext = ∅ ∧ s.cfg.autoLeave = false)

/-- `checkAndReturn`: the state if `checkInvariants` accepts it. -/
def checkedM (s : CCState) : Option CCState := if CfgInv s then some s else none

theorem checkedM_some {s s' : CCState} (h : checkedM s = some s') : s' = s ∧ CfgInv s := by
  unfold checkedM at h
  split at h
  · rename_i hc; cases h; exact ⟨rfl, hc⟩
  · cases h

/-- What `checkAndCopy` copies: `Config.Clone` does not copy `AutoLeave`. -/
def clearAutoLeave (s : CCState) : CCState :=
  { cfg := { s.cfg with autoLeave := false }, prs := s.prs }

/-- `remove(id)` on the configuration, when `id` is tracked: out of the incoming voters,
the learners and the staged learners, and (2026-10-20, witness support) no longer the incoming
witness if it was (`Witnesses[0] = 0`). -/
def removeCfg (id : w64) (c : CfgM) : CfgM :=
  { c with incoming := GMap.delete id c.incoming, learners := GMap.delete id c.learners,
           learnersNext := GMap.delete id c.learnersNext,
           wit := if id = c.wit then W64 0 else c.wit }

/-- Without a witness `removeCfg` touches only the three sets. -/
theorem removeCfg_nw {id : w64} {c : CfgM} (h : c.wit = W64 0) :
    removeCfg id c =
      { c with incoming := GMap.delete id c.incoming, learners := GMap.delete id c.learners,
               learnersNext := GMap.delete id c.learnersNext } := by
  unfold removeCfg; rw [h]; split <;> rfl

/-- `Changer.remove(id)`: nothing for an untracked id; otherwise out of the incoming
voters and the learner sets, and untracked unless it is an outgoing voter. -/
def removeM (id : w64) (s : CCState) : CCState :=
  if id ∈ s.prs then
    { cfg := removeCfg id s.cfg,
      prs := if id ∈ s.cfg.outgoing then s.prs else GMap.delete id s.prs }
  else s

/-- `Changer.initProgress(id, isLearner)` on an untracked id: an incoming voter or a
learner, tracked with a fresh `Progress`. -/
def initProgressM (id : w64) (isLearner : Bool) (s : CCState) : CCState :=
  { cfg := if isLearner then { s.cfg with learners := <[id := ()]> s.cfg.learners }
           else { s.cfg with incoming := <[id := ()]> s.cfg.incoming },
    prs := <[id := isLearner]> s.prs }

/-- `Changer.initProgress(id, false, true)` (2026-10-20, witness support): an untracked id
becomes an incoming voter and the incoming witness, tracked with a fresh `Progress`. -/
def initWitnessM (id : w64) (s : CCState) : CCState :=
  { cfg := { s.cfg with incoming := <[id := ()]> s.cfg.incoming, wit := id },
    prs := <[id := false]> s.prs }

/-- `Changer.makeWitness(id)` (2026-10-20, witness support): the error "cannot have more than
one witness in incoming" if another id is the incoming witness; an untracked id via
`initProgress` as the witness; the tracked witness (its `Progress` has `IsWitness`: the incoming
witness, `ownPrsW`'s `WitT`) back among the incoming voters, where it is (`ownCfgCCw`), so
unchanged; any other tracked id is the error
"cannot change non-witness voter/learner to witness". -/
def makeWitnessM (id : w64) (s : CCState) : Option CCState :=
  if s.cfg.wit ≠ W64 0 ∧ s.cfg.wit ≠ id then none
  else if id ∉ s.prs then some (initWitnessM id s)
  else if id = s.cfg.wit then some s
  else none

/-- `Changer.makeVoter(id)`: a new id via `initProgress`; a tracked one is marked a
non-learner, leaves both learner sets and joins the incoming voters. -/
def makeVoterM (id : w64) (s : CCState) : CCState :=
  if id ∈ s.prs then
    { cfg := { s.cfg with incoming := <[id := ()]> s.cfg.incoming,
                          learners := GMap.delete id s.cfg.learners,
                          learnersNext := GMap.delete id s.cfg.learnersNext },
      prs := <[id := false]> s.prs }
  else initProgressM id false s

/-- `Changer.makeLearner(id)`: a new id via `initProgress`; a learner stays one; any other
tracked id is removed (keeping its `Progress`) and then staged in `LearnersNext` if it is
an outgoing voter, made a learner otherwise. -/
def makeLearnerM (id : w64) (s : CCState) : CCState :=
  match s.prs !! id with
  | none => initProgressM id true s
  | some true => s
  | some false =>
    if id ∈ s.cfg.outgoing then
      { cfg := { removeCfg id s.cfg with
                   learnersNext := <[id := ()]> (GMap.delete id s.cfg.learnersNext) },
        prs := s.prs }
    else
      { cfg := { removeCfg id s.cfg with
                   learners := <[id := ()]> (GMap.delete id s.cfg.learners) },
        prs := <[id := true]> s.prs }

/-- `Changer.makeVoter(id)` with its error (2026-10-20, witness support): "cannot change witness
to non-witness voter" at the tracked witness (`makeVoterM` otherwise). -/
def makeVoterO (id : w64) (s : CCState) : Option CCState :=
  if id ∈ s.prs ∧ id = s.cfg.wit ∧ s.cfg.wit ≠ W64 0 then none else some (makeVoterM id s)

/-- `Changer.makeLearner(id)` with its error (2026-10-20, witness support): "cannot change witness
to non-witness learner" at the tracked witness not a learner (`makeLearnerM` otherwise). -/
def makeLearnerO (id : w64) (s : CCState) : Option CCState :=
  if s.prs !! id = some false ∧ id = s.cfg.wit ∧ s.cfg.wit ≠ W64 0 then none
  else some (makeLearnerM id s)

/-- Without a witness `makeVoter` and `makeLearner` do not fail. -/
theorem makeVoterO_nw {id : w64} {s : CCState} (h : s.cfg.wit = W64 0) :
    makeVoterO id s = some (makeVoterM id s) := by
  unfold makeVoterO; rw [h]; simp

theorem makeLearnerO_nw {id : w64} {s : CCState} (h : s.cfg.wit = W64 0) :
    makeLearnerO id s = some (makeLearnerM id s) := by
  unfold makeLearnerO; rw [h]; simp

/-- One change of `Changer.apply`'s loop: `NodeId = 0` is skipped; `AddNode` (`0`),
`AddLearnerNode` (`3`), `RemoveNode` (`1`), `UpdateNode` (`2`, nothing) and (2026-10-20, witness
support) `AddWitness` (`4`) by type; any other type is the error "unexpected conf type". The
witness's `Progress` (tracked, the incoming witness) is not converted: `makeVoter`'s error, and
`makeLearner`'s unless it is a learner already. -/
def applyOne (cc : ConfChangeSingleM) (s : CCState) : Option CCState :=
  if cc.NodeId' = W64 0 then some s
  else if cc.Type' = W32 0 then makeVoterO cc.NodeId' s
  else if cc.Type' = W32 3 then makeLearnerO cc.NodeId' s
  else if cc.Type' = W32 1 then some (removeM cc.NodeId' s)
  else if cc.Type' = W32 2 then some s
  else if cc.Type' = W32 4 then makeWitnessM cc.NodeId' s
  else none

/-- What a change keeps (2026-10-20, witness support): the outgoing voters, and no witness
without an `AddWitness` (`Changer.apply`'s premise and loop invariant). -/
theorem makeVoterM_shape (id : w64) (s : CCState) :
    (makeVoterM id s).cfg.outgoing = s.cfg.outgoing ∧ (makeVoterM id s).cfg.wit = s.cfg.wit := by
  unfold makeVoterM initProgressM
  split <;> simp

theorem removeM_shape (id : w64) (s : CCState) :
    (removeM id s).cfg.outgoing = s.cfg.outgoing ∧
      (s.cfg.wit = W64 0 → (removeM id s).cfg.wit = W64 0) := by
  unfold removeM removeCfg
  split
  · refine ⟨rfl, fun h => ?_⟩
    simp only [h]; split <;> rfl
  · exact ⟨rfl, fun h => h⟩

theorem makeLearnerM_shape (id : w64) (s : CCState) :
    (makeLearnerM id s).cfg.outgoing = s.cfg.outgoing ∧
      (s.cfg.wit = W64 0 → (makeLearnerM id s).cfg.wit = W64 0) := by
  unfold makeLearnerM initProgressM
  split
  · exact ⟨rfl, fun h => h⟩
  · exact ⟨rfl, fun h => h⟩
  · split
    · refine ⟨rfl, fun h => ?_⟩
      simp only [removeCfg, h]; split <;> rfl
    · refine ⟨rfl, fun h => ?_⟩
      simp only [removeCfg, h]; split <;> rfl

theorem applyOne_shape {cc : ConfChangeSingleM} {s s'' : CCState} (h : applyOne cc s = some s'') :
    s''.cfg.outgoing = s.cfg.outgoing ∧
      ((cc.NodeId' = W64 0 ∨ cc.Type' ≠ W32 4) → s.cfg.wit = W64 0 → s''.cfg.wit = W64 0) := by
  unfold applyOne at h
  split at h
  · cases h; exact ⟨rfl, fun _ h => h⟩
  split at h
  · unfold makeVoterO at h
    split at h
    · cases h
    · cases h
      exact ⟨(makeVoterM_shape _ _).1, fun _ h => (makeVoterM_shape _ _).2.trans h⟩
  split at h
  · unfold makeLearnerO at h
    split at h
    · cases h
    · cases h
      exact ⟨(makeLearnerM_shape _ _).1, fun _ h => (makeLearnerM_shape _ _).2 h⟩
  split at h
  · cases h
    exact ⟨(removeM_shape _ _).1, fun _ h => (removeM_shape _ _).2 h⟩
  split at h
  · cases h; exact ⟨rfl, fun _ h => h⟩
  split at h
  · rename_i h0 _ _ _ _ h4
    refine ⟨?_, fun hc => absurd h4 (hc.resolve_left h0)⟩
    unfold makeWitnessM initWitnessM at h
    revert h
    split
    · intro h; cases h
    split
    · intro h; cases h; rfl
    split
    · intro h; cases h; rfl
    · intro h; cases h
  · cases h

/-- `Changer.apply`'s loop invariant (2026-10-20, witness support): the outgoing voters are the
start's, and a joint configuration has no witness, given no `AddWitness` at a joint one. -/
theorem apply_inv {s s' s'' : CCState} {cc : ConfChangeSingleM}
    (Hinv : s'.cfg.outgoing = s.cfg.outgoing ∧ (s.cfg.outgoing = ∅ ∨ s'.cfg.wit = W64 0))
    (h : applyOne cc s' = some s'')
    (Hno4 : s.cfg.outgoing ≠ ∅ → cc.NodeId' = W64 0 ∨ cc.Type' ≠ W32 4) :
    s''.cfg.outgoing = s.cfg.outgoing ∧ (s.cfg.outgoing = ∅ ∨ s''.cfg.wit = W64 0) := by
  obtain ⟨ho, hw⟩ := applyOne_shape h
  refine ⟨ho.trans Hinv.1, ?_⟩
  by_cases hj : s.cfg.outgoing = ∅
  · exact .inl hj
  · exact .inr (hw (Hno4 hj) (Hinv.2.resolve_left hj))

/-- The changes one after the other; the first error stops it. -/
def applyAll : List ConfChangeSingleM → CCState → Option CCState
  | [], s => some s
  | cc :: ccs, s => (applyOne cc s).bind (applyAll ccs)

/-- `Changer.apply(ccs)`: the changes, then the error "removed all voters" if no incoming
voter is left. -/
def applyM (ccs : List ConfChangeSingleM) (s : CCState) : Option CCState :=
  (applyAll ccs s).bind fun s' => if s'.cfg.incoming = ∅ then none else some s'

/-- `symdiff(l, r)`: the size of the symmetric difference. -/
def symdiffN (l r : GSet w64) : Nat := GMap.size (l \ r) + GMap.size (r \ l)

/-- `Simple`'s check `symdiff(...) > 1`, on Go's `int`: the count wraps past `2^63 - 1`
(below that it is `1 < symdiffN l r`, `symdiffTooBig_iff`). -/
def SymdiffTooBig (l r : GSet w64) : Prop := 1 < sint.Z (W64 (symdiffN l r : Int))

/-- `Changer.Simple(ccs)` on a tracker in state `s`: `checkAndCopy` (whose copy has
`AutoLeave` off), the error "can't apply simple config change in joint config", `apply`,
the error "more than one voter changed without entering joint config" (against the
tracker's own incoming voters), `checkAndReturn`. -/
def simpleM (ccs : List ConfChangeSingleM) (s : CCState) : Option CCState :=
  if ¬ CfgInv (clearAutoLeave s) then none
  else if s.cfg.outgoing ≠ ∅ then none
  else match applyM ccs (clearAutoLeave s) with
    | none => none
    | some s1 => if SymdiffTooBig s.cfg.incoming s1.cfg.incoming then none else checkedM s1

/-- `Changer.EnterJoint(autoLeave, ccs)`: `checkAndCopy`, the errors "config is already
joint" and "can't make a zero-voter config joint", the outgoing voters a copy of the
incoming ones, `apply`, `AutoLeave` set, `checkAndReturn`. -/
def enterJointM (autoLeave : Bool) (ccs : List ConfChangeSingleM) (s : CCState) :
    Option CCState :=
  if ¬ CfgInv (clearAutoLeave s) then none
  else if s.cfg.outgoing ≠ ∅ then none
  else if s.cfg.incoming = ∅ then none
  else match applyM ccs { cfg := { s.cfg with outgoing := s.cfg.incoming, autoLeave := false },
                          prs := s.prs } with
    | none => none
    | some s1 => checkedM { cfg := { s1.cfg with autoLeave := autoLeave }, prs := s1.prs }

/-- `LeaveJoint`'s transition: the staged learners become learners (marked so), the
outgoing voters that are neither incoming voters nor learners are untracked, the outgoing
config and `LearnersNext` are emptied, `AutoLeave` is off. -/
def leaveJointState (s : CCState) : CCState :=
  { cfg := { incoming := s.cfg.incoming, outgoing := ∅,
             learners := s.cfg.learners ∪ s.cfg.learnersNext, learnersNext := ∅,
             -- (2026-10-20, witness support) `Witnesses[0]` is kept (until then dropped)
             autoLeave := false, wit := s.cfg.wit },
    prs := GMap.filter (fun k _ => decide (k ∈ s.cfg.incoming ∨
              k ∈ s.cfg.learners ∪ s.cfg.learnersNext ∨ k ∉ s.cfg.outgoing))
            (GMap.fmap (fun _ => true)
              (GMap.filter (fun k _ => decide (k ∈ s.cfg.learnersNext)) s.prs) ∪ s.prs) }

/-- `Changer.LeaveJoint()`: `checkAndCopy`, the error "can't leave a non-joint config",
the transition, `checkAndReturn`. -/
def leaveJointM (s : CCState) : Option CCState :=
  if ¬ CfgInv (clearAutoLeave s) then none
  else if s.cfg.outgoing = ∅ then none
  else checkedM (leaveJointState s)

end model

theorem applyAll_append [GooseExts] (l1 l2 : List ConfChangeSingleM) (s : CCState) :
    applyAll (l1 ++ l2) s = (applyAll l1 s).bind (applyAll l2) := by
  induction l1 generalizing s with
  | nil => simp [applyAll]
  | cons y l ih =>
    simp only [List.cons_append, applyAll]
    cases applyOne y s with
    | none => rfl
    | some s' => simp [ih]

theorem applyAll_snoc [GooseExts] (l : List ConfChangeSingleM)
    (x : ConfChangeSingleM) (s : CCState) :
    applyAll (l ++ [x]) s = (applyAll l s).bind (applyOne x) := by
  induction l generalizing s with
  | nil => simp [applyAll]
  | cons y l ih =>
    simp only [List.cons_append, applyAll]
    cases applyOne y s with
    | none => rfl
    | some s' => simp [ih]

/-- Two maps with the same domain have the same members. -/
theorem mem_of_domSet_eq {V V' : Type} {a : GMap w64 V} {b : GMap w64 V'}
    (h : domSet a = domSet b) (k : w64) : k ∈ a ↔ k ∈ b := by
  rw [← GMap.elem_of_dom', h, GMap.elem_of_dom']

proj_simps Perennial.EtcdGrove.clearAutoLeave Perennial.EtcdGrove.removeCfg
  Perennial.EtcdGrove.initProgressM Perennial.EtcdGrove.leaveJointState

/-- A voters-only, non-joint `Config` value: the incoming voter map is `v`; the outgoing
voter map, `Learners` and `LearnersNext` are `nil`. What `Restore.spec` says of the
configuration it starts from (`MakeProgressTracker`'s), and all `Config.Clone` reads. -/
def ConfigVotersOnly [GooseExts] (cfg : tracker.Config) (v : Loc) : Prop :=
  cfg.Voters'.arr = [v, map.nil] ∧ cfg.Learners' = map.nil ∧ cfg.LearnersNext' = map.nil

/-- `ConfigVotersOnly`, and `AutoLeave` off: what Go's `checkInvariants` requires of a
non-joint config, and what `Config.Clone` produces (it does not copy `AutoLeave`). -/
def ConfigSimple [GooseExts] (cfg : tracker.Config) (v : Loc) : Prop :=
  ConfigVotersOnly cfg v ∧ cfg.AutoLeave' = false

/-- `pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeId: id}`. -/
abbrev addNodeCC [GooseExts] (id : w64) : ConfChangeSingleM :=
  { Type' := W32 0, NodeId' := id }

/-- `pb.ConfChangeSingle{Type: pb.ConfChangeAddLearnerNode, NodeId: id}` (2026-10-13). -/
abbrev addLearnerCC [GooseExts] (id : w64) : ConfChangeSingleM :=
  { Type' := W32 3, NodeId' := id }

/-- No `Progress` of the map is a witness's (raft#168's `IsWitness`): the confchange specs are
of witness-free configurations (`notes/pr-verify/raft-168.md`). -/
def NoWit [GooseExts] (pvs : GMap w64 tracker.Progress) : Prop :=
  ∀ k pv, pvs !! k = some pv → pv.IsWitness' = false

/-- (2026-10-20, witness support) The `Progress` with `IsWitness` is the incoming witness's `w`
(none at `w = 0`: `WitT_zero`), and the witness is tracked: what the confchange specs keep of the flags. A configuration
with a witness the incoming half removed while the outgoing half keeps it (Go's `Witnesses =
[0, W]` with `W` tracked) is outside it, as outside `CfgM` (`notes/raft-witness.md`, `NoOutWit`). -/
def WitT [GooseExts] (w : w64) (pvs : GMap w64 tracker.Progress) : Prop :=
  (w ≠ W64 0 → (pvs !! w).isSome) ∧
  ∀ k pv, pvs !! k = some pv → pv.IsWitness' = decide (k = w ∧ w ≠ W64 0)

theorem WitT_zero [GooseExts] {pvs : GMap w64 tracker.Progress} : WitT (W64 0) pvs ↔ NoWit pvs := by
  constructor
  · intro h k pv hk; rw [h.2 k pv hk]; simp
  · intro h; exact ⟨fun h0 => absurd rfl h0, fun k pv hk => by rw [h k pv hk]; simp⟩

/-- A fresh `Progress` keeps `WitT` when its flag is the witness's. -/
theorem WitT.insert [GooseExts] {w : w64} {pvs : GMap w64 tracker.Progress} {id : w64}
    {pv : tracker.Progress} (H : WitT w pvs) (Hpv : pv.IsWitness' = decide (id = w ∧ w ≠ W64 0)) :
    WitT w (<[id := pv]> pvs) := by
  refine ⟨fun h => ?_, fun k q hq => ?_⟩
  · by_cases hk : id = w
    · subst hk; rw [GMap.lookup_insert_eq]; rfl
    · rw [GMap.lookup_insert_ne _ _ hk]; exact H.1 h
  · by_cases hk : id = k
    · subst hk; rw [GMap.lookup_insert_eq] at hq; cases hq; exact Hpv
    · rw [GMap.lookup_insert_ne _ _ hk] at hq; exact H.2 k q hq

/-- Changing a tracked `Progress`'s `IsLearner` keeps `WitT`. -/
theorem WitT.set_learner [GooseExts] {w : w64} {pvs : GMap w64 tracker.Progress} {id : w64}
    {pv : tracker.Progress} (b : Bool) (H : WitT w pvs) (Hpv : pvs !! id = some pv) :
    WitT w (<[id := { pv with IsLearner' := b }]> pvs) :=
  H.insert (H.2 id pv Hpv)

/-- Untracking an id other than the witness keeps `WitT`. -/
theorem WitT.delete [GooseExts] {w : w64} {pvs : GMap w64 tracker.Progress} {id : w64}
    (H : WitT w pvs) (Hid : w ≠ W64 0 → id ≠ w) : WitT w (GMap.delete id pvs) := by
  refine ⟨fun h => ?_, fun k q hq => ?_⟩
  · rw [GMap.lookup_delete_ne _ (fun e => Hid h e)]; exact H.1 h
  · by_cases hk : id = k
    · subst hk; rw [GMap.lookup_delete] at hq; cases hq
    · rw [GMap.lookup_delete_ne _ hk] at hq; exact H.2 k q hq

/-- Untracking the witness leaves none (`remove` clears `Witnesses[0]`). -/
theorem WitT.delete_wit [GooseExts] {w : w64} {pvs : GMap w64 tracker.Progress}
    (H : WitT w pvs) : WitT (W64 0) (GMap.delete w pvs) := by
  refine ⟨fun h => absurd rfl h, fun k q hq => ?_⟩
  by_cases hk : w = k
  · subst hk; rw [GMap.lookup_delete] at hq; cases hq
  · rw [GMap.lookup_delete_ne _ hk] at hq
    rw [H.2 k q hq]; simp [Ne.symm hk]

/-- A fresh witness's `Progress` at a configuration without one. -/
theorem WitT.insert_wit [GooseExts] {pvs : GMap w64 tracker.Progress} {id : w64}
    {pv : tracker.Progress} (H : WitT (W64 0) pvs) (Hid : id ≠ W64 0) (Hpv : pv.IsWitness' = true) :
    WitT id (<[id := pv]> pvs) := by
  refine ⟨fun _ => by rw [GMap.lookup_insert_eq]; rfl, fun k q hq => ?_⟩
  by_cases hk : id = k
  · subst hk; rw [GMap.lookup_insert_eq] at hq; cases hq; rw [Hpv]; simpa using Hid
  · rw [GMap.lookup_insert_ne _ _ hk] at hq
    rw [H.2 k q hq]; simp [Ne.symm hk]

/-- The model of a progress map's values: each id's `IsLearner`. -/
def flagsOf [GooseExts] (pvs : GMap w64 tracker.Progress) : GMap w64 Bool :=
  GMap.fmap (fun pv => pv.IsLearner') pvs

/-- A `Progress` as `initProgress` allocates it: `Match = 0`, `Next = max(LastIndex, 1)`,
recently active, `StateProbe` and the other fields zero; its `Inflights` fresh, its
`IsLearner` whatever was asked (and possibly changed since). -/
def FreshPr [GooseExts] (chg : confchange.Changer) (pv : tracker.Progress) : Prop :=
  pv.Match' = W64 0 ∧ uint.Z pv.Next' = max (uint.Z chg.LastIndex') 1 ∧
  pv.sentCommit' = W64 0 ∧ pv.State' = W64 0 ∧ pv.PendingSnapshot' = W64 0 ∧
  pv.RecentActive' = true ∧ pv.MsgAppFlowPaused' = false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The triple of one of `chain`'s ops. `chain` calls `op(chg)` with the `Changer`
*value* whose tracker holds the current `Config` and progress map, and stores what the
op returns back into them; so an op is specified on every such value, from `P` on the
pair it is handed to `Q` on the pair it returns, with no error. -/
def opSpec (f : GoFunc) (chg : confchange.Changer)
    (P Q : tracker.Config → Loc → IProp GF) : IProp GF :=
  iprop(∀ (cfg : tracker.Config) (prs : Loc),
    {{ P cfg prs }}
      (App (Val #f)
        (Val #({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
          confchange.Changer)))
    {{ (cfg' : tracker.Config) (prs' : Loc), RET (PairV (PairV #cfg' #prs') #interface.nil);
        Q cfg' prs' }})

instance opSpec_persistent (f : GoFunc) (chg : confchange.Changer)
    (P Q : tracker.Config → Loc → IProp GF) : Persistent (opSpec f chg P Q) := by
  unfold opSpec; infer_instance

/-! ### The representation of the model (2026-10-12) -/

/-- A `tracker.Config` value represents `c`, its maps read at `dq`: the incoming voter
map is a map (never `nil`: `makeVoter` writes into it); the outgoing voter map,
`Learners` and `LearnersNext` are canonical (`ownIdsetC`: `nil` exactly when empty).
`checkInvariants` requires canonicity of the first and the last of a non-joint config;
every `Changer` operation keeps all three canonical (`nilAwareAdd`/`nilAwareDelete`, the
`nil` writes of `LeaveJoint`, `Config.Clone` copying `nil` as `nil`), and the trackers raft
builds start canonical (`MakeProgressTracker`'s are `nil`). A tracker with an empty
non-`nil` `Learners` map, which no `confchange` operation creates, is outside these specs:
the canonical representation is what lets `Restore`'s statement promise `Learners = nil`. -/
def ownCfgCCw (w : w64) (cfg : tracker.Config) (dq : DFrac) (c : CfgM) : IProp GF :=
  iprop(∃ (vin vout : Loc),
    "%Harr" ∷ ⌜cfg.Voters'.arr = [vin, vout]⌝ ∗
    "Hin" ∷ vin ↦${dq} c.incoming ∗
    "Hout" ∷ ownIdsetC vout dq c.outgoing ∗
    "Hl" ∷ ownIdsetC cfg.Learners' dq c.learners ∗
    "Hln" ∷ ownIdsetC cfg.LearnersNext' dq c.learnersNext ∗
    "%Hal" ∷ ⌜cfg.AutoLeave' = c.autoLeave⌝ ∗
    -- the witness (raft#168): `w` in the incoming half, none in the outgoing one (2026-10-20,
    -- witness support: `ownTrackerC` at its configuration's `wit`), and an incoming voter
    -- (`checkInvariants`'s witness check, which every `Changer` operation keeps: `remove` clears
    -- `Witnesses[0]`, `makeLearner` refuses the witness)
    "%Hwit" ∷ ⌜cfg.Witnesses'.arr = [w, W64 0] ∧ (w ≠ W64 0 → w ∈ c.incoming)⌝)

/-- A configuration's representation at its witness (raft#168; until 2026-10-20 at `0`, the
specs witness-free): what `confchange`'s specs take and give. -/
abbrev ownCfgCC (cfg : tracker.Config) (dq : DFrac) (c : CfgM) : IProp GF :=
  ownCfgCCw c.wit cfg dq c

theorem ownCfgCC_elim {w : w64} (cfg : tracker.Config) (dq : DFrac) (c : CfgM) :
    ownCfgCCw (GF := GF) w cfg dq c ⊢ ∃ (vin vout : Loc),
      ⌜cfg.Voters'.arr = [vin, vout]⌝ ∗ vin ↦${dq} c.incoming ∗ ownIdsetC vout dq c.outgoing ∗
      ownIdsetC cfg.Learners' dq c.learners ∗ ownIdsetC cfg.LearnersNext' dq c.learnersNext ∗
      ⌜cfg.AutoLeave' = c.autoLeave⌝ ∗
      ⌜cfg.Witnesses'.arr = [w, W64 0] ∧ (w ≠ W64 0 → w ∈ c.incoming)⌝ := by
  unfold ownCfgCCw
  iintro H
  iNamed H
  iexists vin, vout
  iframe
  ipureintro; exact ⟨Harr, Hal, Hwit⟩

theorem ownCfgCC_intro {w : w64} (cfg : tracker.Config) (dq : DFrac) (c : CfgM) (vin vout : Loc)
    (Harr : cfg.Voters'.arr = [vin, vout]) (Hal : cfg.AutoLeave' = c.autoLeave)
    (Hwit : cfg.Witnesses'.arr = [w, W64 0] ∧ (w ≠ W64 0 → w ∈ c.incoming)) :
    ⊢ (vin ↦${dq} c.incoming : IProp GF) -∗ ownIdsetC vout dq c.outgoing -∗
      ownIdsetC cfg.Learners' dq c.learners -∗ ownIdsetC cfg.LearnersNext' dq c.learnersNext -∗
      ownCfgCCw w cfg dq c := by
  iintro Hin Hout Hl Hln
  unfold ownCfgCCw
  iexists vin, vout
  simp only [named]
  iframe
  ipureintro; exact ⟨Harr, Hal, Hwit⟩

/-- The tracker a `Changer` starts from: its configuration, its progress map (at `dqm`)
and the `Progress` objects (at `dqp`), whose values are `pvs`. `confchange` only reads
them (`checkAndCopy` copies them), so any fractions do. -/
def ownTrackerCC (tv : tracker.ProgressTracker) (dqc dqm dqp : DFrac) (c : CfgM)
    (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress) : IProp GF :=
  iprop(ownCfgCC tv.Config' dqc c ∗ tv.Progress' ↦${dqm} prs ∗
    ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗ ⌜WitT c.wit pvs⌝)

/-- A `Progress` of a `Changer`'s result, at id `id`: a copy of the tracker's (`base`, the
values the `Changer` started from) with only `IsLearner` changed, or a fresh one
(`initProgress`) with its fresh `Inflights`. A copy shares the original's `Inflights`
pointer (`checkAndCopy`'s `ppr := *pr`), so its ring is whatever owns the original's. -/
def ownNewPr (chg : confchange.Changer) (base : GMap w64 tracker.Progress) (id : w64)
    (pv : tracker.Progress) : IProp GF :=
  iprop(⌜∃ pv0, base !! id = some pv0 ∧ pv = { pv0 with IsLearner' := pv.IsLearner' }⌝ ∨
    (⌜FreshPr chg pv⌝ ∗
      ownInflights pv.Inflights' (inflightsNew chg.Tracker'.MaxInflight'
        chg.Tracker'.MaxInflightBytes')))

/-- A progress map a `Changer` builds, in state `p` (each id's `IsLearner`): the map, the
`Progress` objects it points at (owned), and what each is (`ownNewPr`). -/
def ownPrsW (chg : confchange.Changer) (base : GMap w64 tracker.Progress) (trk : Loc)
    (w : w64) (p : GMap w64 Bool) : IProp GF :=
  iprop(∃ (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress),
    "Htrk" ∷ trk ↦$ prs ∗
    "Hprs" ∷ ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦ pv) ∗
    "%Hflags" ∷ ⌜flagsOf pvs = p⌝ ∗
    -- (2026-10-20, witness support) the witness's `Progress` is the incoming witness's
    "%Hwt" ∷ ⌜WitT w pvs⌝ ∗
    "Hnew" ∷ ([∗map] k ↦ pv ∈ pvs, ownNewPr chg base k pv))

/-- The `Config` in the variable `cfgp` (a `Changer` method's local, passed by pointer to
`apply`, `makeVoter`, ...), owned, representing `c`. -/
def ownCfgAt (cfgp : Loc) (c : CfgM) : IProp GF :=
  iprop(∃ cfg, cfgp ↦ cfg ∗ ownCfgCC cfg (DFrac.own 1) c)

/-- The state a `Changer` method works on: the `Config` at `cfgp` and the progress map
`trk`. -/
def ownWork (chg : confchange.Changer) (base : GMap w64 tracker.Progress) (cfgp trk : Loc)
    (s : CCState) : IProp GF :=
  iprop(ownCfgAt cfgp s.cfg ∗ ownPrsW chg base trk s.cfg.wit s.prs)

/-- What a `Changer` method that works on `ownWork` leaves for the model's answer `r`
(2026-10-20, witness support: `makeVoter`, `makeLearner`, `makeWitness` can fail): an error
on `none`; on `some s`, `nil` and the state `s`. -/
def ownWorkO (chg : confchange.Changer) (base : GMap w64 tracker.Progress) (cfgp trk : Loc)
    (r : Option CCState) (err : GoInterface) : IProp GF :=
  match r with
  | none => iprop(⌜err ≠ interface.nil⌝)
  | some s => iprop(⌜err = interface.nil⌝ ∗ ownWork chg base cfgp trk s)

/-- What a `Changer` method returns, `(cfg, trk, err)`, for the model's answer `r`: an
error (non-`nil`) on `none`; on `some s`, `nil` with a fresh configuration and progress
map in state `s`. -/
def ownResult (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (r : Option CCState) (cfg : tracker.Config) (trk : Loc) (err : GoInterface) : IProp GF :=
  match r with
  | none => iprop(⌜err ≠ interface.nil⌝)
  | some s => iprop(⌜err = interface.nil⌝ ∗ ownCfgCC cfg (DFrac.own 1) s.cfg ∗
      ownPrsW chg base trk s.cfg.wit s.prs)

end defs

@[simp] theorem flagsOf_insert [GooseExts] (pvs : GMap w64 tracker.Progress) (k : w64)
    (pv : tracker.Progress) : flagsOf (<[k := pv]> pvs) = <[k := pv.IsLearner']> (flagsOf pvs) :=
  GMap.fmap_insert _ _ _ _

@[simp] theorem flagsOf_delete [GooseExts] (pvs : GMap w64 tracker.Progress) (k : w64) :
    flagsOf (GMap.delete k pvs) = GMap.delete k (flagsOf pvs) :=
  GMap.fmap_delete _ _ _

/-- `IsLearner` in the model is the `Progress`'s. -/
theorem flagsOf_lookup [GooseExts] (pvs : GMap w64 tracker.Progress) (k : w64)
    (pv : tracker.Progress) (h : pvs !! k = some pv) : flagsOf pvs !! k = some pv.IsLearner' := by
  simp [flagsOf, GMap.lookup_fmap, h]

theorem flagsOf_mem [GooseExts] (pvs : GMap w64 tracker.Progress) (k : w64) :
    k ∈ flagsOf pvs ↔ (pvs !! k).isSome := by
  simp [flagsOf, GMap.mem_iff, GMap.lookup_fmap]

theorem flagsOf_lookup' [GooseExts] (pvs : GMap w64 tracker.Progress) (k : w64) :
    flagsOf pvs !! k = (pvs !! k).map (fun pv => pv.IsLearner') := by
  simp [flagsOf, GMap.lookup_fmap]

/-! ### Lemmas on the representation -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem ownWork_elim (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (cfgp trk : Loc) (s : CCState) :
    ownWork (GF := GF) chg base cfgp trk s ⊢ ∃ (cfg : tracker.Config) (prs : GMap w64 Loc)
      (pvs : GMap w64 tracker.Progress),
      cfgp ↦ cfg ∗ ownCfgCC cfg (DFrac.own 1) s.cfg ∗ trk ↦$ prs ∗
      ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦ pv) ∗ ⌜flagsOf pvs = s.prs⌝ ∗ ⌜WitT s.cfg.wit pvs⌝ ∗
      ([∗map] k ↦ pv ∈ pvs, ownNewPr chg base k pv) := by
  unfold ownWork ownCfgAt ownPrsW
  iintro ⟨⟨%cfg, Hcfgp, Hc⟩, ⟨%prs, %pvs, Htrk, Hprs, %Hflags, %Hwt, Hnew⟩⟩
  iexists cfg, prs, pvs
  iframe
  isplitr; · ipureintro; exact Hflags
  ipureintro; exact Hwt

theorem ownWork_intro (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (cfgp trk : Loc) (s : CCState) (cfg : tracker.Config) (prs : GMap w64 Loc)
    (pvs : GMap w64 tracker.Progress) (Hflags : flagsOf pvs = s.prs) (Hwt : WitT s.cfg.wit pvs) :
    ⊢ (cfgp ↦ cfg : IProp GF) -∗ ownCfgCC cfg (DFrac.own 1) s.cfg -∗ trk ↦$ prs -∗
      ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦ pv) -∗
      ([∗map] k ↦ pv ∈ pvs, ownNewPr chg base k pv) -∗
      ownWork chg base cfgp trk s := by
  iintro Hcfgp Hc Htrk Hprs Hnew
  unfold ownWork ownCfgAt ownPrsW
  isplitl [Hcfgp Hc]
  · iexists cfg; iframe
  iexists prs, pvs
  simp only [named]
  iframe
  ipureintro; exact ⟨Hflags, Hwt⟩

/-- Changing a `Progress`'s `IsLearner` keeps what it is (a copy of the tracker's, or a
fresh one). -/
theorem ownNewPr_set_learner (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (id : w64) (pv : tracker.Progress) (b : Bool) :
    ownNewPr (GF := GF) chg base id pv ⊢ ownNewPr chg base id { pv with IsLearner' := b } := by
  unfold ownNewPr
  iintro (%H | ⟨%Hf, Hinfl⟩)
  · ileft; ipureintro
    obtain ⟨pv0, h0, h1⟩ := H
    refine ⟨pv0, h0, ?_⟩
    rw [h1]
  · iright
    iframe Hinfl
    ipureintro
    exact Hf

/-- The tracker a `Changer` reads: its `Progress` flags (`WitT`, read out). -/
theorem ownTrackerCC_witT (tv : tracker.ProgressTracker) (dqc dqm dqp : DFrac) (c : CfgM)
    (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress) :
    ownTrackerCC (GF := GF) tv dqc dqm dqp c prs pvs ⊢
      ownTrackerCC tv dqc dqm dqp c prs pvs ∗ ⌜WitT c.wit pvs⌝ := by
  unfold ownTrackerCC
  iintro ⟨H1, H2, H3, %Hnw⟩
  iframe H1 H2 H3
  isplitr <;> ipureintro <;> exact Hnw

/-- Borrow the `Progress` of a tracked id from a progress map, to read it or to set its
`IsLearner`. -/
theorem ownPrs_borrow (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress) (id : w64) (pr : Loc)
    (pv : tracker.Progress) (hpr : prs !! id = some pr) (hpv : pvs !! id = some pv) :
    ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦ pv) ∗ ([∗map] k ↦ pv ∈ pvs, ownNewPr chg base k pv) ⊢
      (pr ↦ pv : IProp GF) ∗ (∀ b : Bool, pr ↦ { pv with IsLearner' := b } -∗
        ([∗map] _k ↦ pr;pv ∈ prs;(<[id := { pv with IsLearner' := b }]> pvs), pr ↦ pv) ∗
        ([∗map] k ↦ pv ∈ (<[id := { pv with IsLearner' := b }]> pvs), ownNewPr chg base k pv)) := by
  iintro ⟨Hprs, Hnew⟩
  icases (BigSepM2.bigSepM2_delete hpr hpv).1 $$ Hprs with ⟨Hpr, Hprs⟩
  icases (BigSepM.bigSepM_delete (Φ := fun k pv => ownNewPr (GF := GF) chg base k pv) hpv).1 $$
    Hnew with ⟨Hn, Hnew⟩
  iframe Hpr
  iintro %b Hpr
  have e1 : <[id := pr]> (GMap.delete id prs) = prs := by
    rw [GMap.insert_delete_eq, GMap.insert_id _ _ _ hpr]
  have e2 : <[id := { pv with IsLearner' := b }]> (GMap.delete id pvs) =
      (<[id := { pv with IsLearner' := b }]> pvs) := by
    rw [GMap.insert_delete_eq]
  have H1 := (BigSepM2.bigSepM2_insert (PROP := IProp GF)
    (Φ := fun (_ : w64) (pr : Loc) (pv : tracker.Progress) => iprop(pr ↦ pv))
    (m1 := GMap.delete id prs) (m2 := GMap.delete id pvs) (x1 := pr)
    (x2 := { pv with IsLearner' := b }) (GMap.lookup_delete _ _) (GMap.lookup_delete _ _))
  simp only [pm_insert_gmap] at H1
  rw [e1, e2] at H1
  have H2 := (BigSepM.bigSepM_insert (PROP := IProp GF)
    (Φ := fun k pv => ownNewPr (GF := GF) chg base k pv) (m := GMap.delete id pvs)
    (x := { pv with IsLearner' := b }) (GMap.lookup_delete _ _))
  simp only [pm_insert_gmap] at H2
  rw [e2] at H2
  isplitl [Hpr Hprs]
  · iapply H1.2
    iframe
  · iapply H2.2
    iframe Hnew
    iapply ownNewPr_set_learner $$ Hn

/-- Untrack an id: its `Progress` leaves the progress map's resources (it is garbage). -/
theorem ownPrs_delete (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress) (id : w64) :
    ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦ pv) ∗ ([∗map] k ↦ pv ∈ pvs, ownNewPr chg base k pv) ⊢
      ([∗map] _k ↦ pr;pv ∈ GMap.delete id prs;GMap.delete id pvs, (pr ↦ pv : IProp GF)) ∗
      ([∗map] k ↦ pv ∈ GMap.delete id pvs, ownNewPr chg base k pv) := by
  iintro ⟨Hprs, Hnew⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : (prs !! id).isSome ↔ (pvs !! id).isSome := Hdom0 id
  rcases hpr : prs !! id with _ | pr
  · have hpv : pvs !! id = none := by
      rw [hpr] at Hdom
      cases h : pvs !! id with
      | none => rfl
      | some _ => rw [h] at Hdom; simp at Hdom
    rw [GMap.delete_notin _ _ hpr, GMap.delete_notin _ _ hpv]
    iframe
  · obtain ⟨pv, hpv⟩ : ∃ pv, pvs !! id = some pv :=
      Option.isSome_iff_exists.1 (Hdom.1 (by rw [hpr]; rfl))
    icases (BigSepM2.bigSepM2_delete hpr hpv).1 $$ Hprs with ⟨-, Hprs⟩
    icases (BigSepM.bigSepM_delete (Φ := fun k pv => ownNewPr (GF := GF) chg base k pv) hpv).1 $$
      Hnew with ⟨-, Hnew⟩
    simp only [pm_delete_gmap]
    iframe

/-- `checkAndCopy`'s copies, as a `Changer`'s result: each a copy of the tracker's. -/
theorem ownNewPr_copies (chg : confchange.Changer) (pvs : GMap w64 tracker.Progress) :
    ⊢ ([∗map] k ↦ pv ∈ pvs, ownNewPr (GF := GF) chg pvs k pv) := by
  refine BigSepM.bigSepM_intro (P := iprop(emp)) (fun {k v} h => ?_)
  unfold ownNewPr
  iintro -
  ileft
  ipureintro
  exact ⟨v, h, rfl⟩

theorem ownNewPr_elim (chg : confchange.Changer) (base : GMap w64 tracker.Progress) (k : w64)
    (pv : tracker.Progress) :
    ownNewPr (GF := GF) chg base k pv ⊢
      ⌜∃ pv0, base !! k = some pv0 ∧ pv = { pv0 with IsLearner' := pv.IsLearner' }⌝ ∨
      (⌜FreshPr chg pv⌝ ∗ ownInflights pv.Inflights' (inflightsNew chg.Tracker'.MaxInflight'
        chg.Tracker'.MaxInflightBytes')) := by
  unfold ownNewPr; iintro H; iexact H

/-- What a `Changer`'s result's `Progress` objects are, given what the tracker's were: a
resource `R` held for each of the tracker's values `base` (say, its inflight ring) goes to
the copy of it, if any (`Hcopy`), and a fresh `Progress` has its fresh ring (`Hfresh`).
Each tracker value is copied at most once, so each `R` is used at most once. A fact `F` of
every result object (2026-10-20: its witness flag, `ownPrsW`'s `WitT`) is passed to both. -/
theorem ownNewPr_transfer (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (R Q : w64 → tracker.Progress → IProp GF) (F : w64 → tracker.Progress → Prop)
    (Hcopy : ∀ k pv0 pv, base !! k = some pv0 →
      pv = { pv0 with IsLearner' := pv.IsLearner' } → F k pv → R k pv0 ⊢ Q k pv)
    (Hfresh : ∀ k pv, FreshPr chg pv → F k pv →
      ownInflights pv.Inflights' (inflightsNew chg.Tracker'.MaxInflight'
        chg.Tracker'.MaxInflightBytes') ⊢ Q k pv)
    (pvs : GMap w64 tracker.Progress) (HF : ∀ k pv, pvs !! k = some pv → F k pv) :
    ([∗map] k ↦ pv ∈ base, R k pv) ∗ ([∗map] k ↦ pv ∈ pvs, ownNewPr chg base k pv) ⊢
      [∗map] k ↦ pv ∈ pvs, Q k pv := by
  suffices H : ∀ (pvs P : GMap w64 tracker.Progress), (∀ k pv, pvs !! k = some pv → F k pv) →
      (∀ k pv0, (pvs !! k).isSome → base !! k = some pv0 → P !! k = some pv0) →
      ([∗map] k ↦ pv ∈ P, R k pv) ∗ ([∗map] k ↦ pv ∈ pvs, ownNewPr chg base k pv) ⊢
        [∗map] k ↦ pv ∈ pvs, Q k pv from H pvs base HF (fun _ _ _ h => h)
  intro pvs
  refine GMap.map_ind (P := fun pvs => ∀ (P : GMap w64 tracker.Progress),
      (∀ k pv, pvs !! k = some pv → F k pv) →
      (∀ k pv0, (pvs !! k).isSome → base !! k = some pv0 → P !! k = some pv0) →
      ([∗map] k ↦ pv ∈ P, R k pv) ∗ ([∗map] k ↦ pv ∈ pvs, ownNewPr chg base k pv) ⊢
        [∗map] k ↦ pv ∈ pvs, Q k pv) ?_ ?_ pvs
  · intro P _ _
    iintro ⟨-, -⟩
    iapply BigSepM.bigSepM_empty.2
    iempintro
  · intro k pv m Hk IH P HF' HP
    iintro ⟨HP', Hm⟩
    icases (BigSepM.bigSepM_insert (Φ := fun k pv => ownNewPr (GF := GF) chg base k pv) Hk).1 $$
      Hm with ⟨Hn, Hm⟩
    iapply (BigSepM.bigSepM_insert (Φ := Q) Hk).2
    have Hne : ∀ k', (m !! k').isSome → k ≠ k' := by
      intro k' h e; subst e; rw [Hk] at h; cases h
    have Fk : F k pv := HF' k pv (GMap.lookup_insert_eq _ _ _)
    have HFm : ∀ k' pv', m !! k' = some pv' → F k' pv' := fun k' pv' h =>
      HF' k' pv' (by rw [GMap.lookup_insert_ne _ _ (Hne k' (by rw [h]; rfl))]; exact h)
    icases ownNewPr_elim _ _ _ _ $$ Hn with (%Hc | ⟨%Hf, Hinfl⟩)
    · obtain ⟨pv0, h0, h1⟩ := Hc
      have hP : P !! k = some pv0 := HP k pv0 (by simp) h0
      icases (BigSepM.bigSepM_delete (Φ := R) hP).1 $$ HP' with ⟨Hr, HP'⟩
      isplitl [Hr]
      · iapply Hcopy k pv0 pv h0 h1 Fk $$ Hr
      · have HP2 : ∀ k' pv0', (m !! k').isSome → base !! k' = some pv0' →
            (GMap.delete k P) !! k' = some pv0' := by
          intro k' pv0' hk' hb
          rw [GMap.lookup_delete_ne _ (Hne k' hk')]
          exact HP k' pv0' (by rw [GMap.lookup_insert_ne _ _ (Hne k' hk')]; exact hk') hb
        iapply IH (GMap.delete k P) HFm HP2 $$ [HP' Hm]
        iframe Hm
        simp only [pm_delete_gmap]
        iexact HP'
    · isplitl [Hinfl]
      · iapply Hfresh k pv Hf Fk $$ Hinfl
      · have HP2 : ∀ k' pv0', (m !! k').isSome → base !! k' = some pv0' → P !! k' = some pv0' :=
          fun k' pv0' hk' hb =>
            HP k' pv0' (by rw [GMap.lookup_insert_ne _ _ (Hne k' hk')]; exact hk') hb
        iapply IH P HFm HP2 $$ [$HP' $Hm]

end lemmas

end EtcdGrove
end Perennial
