/-
# raft's `confchange` package (batch R4): resources and laws

`confchange.Changer{Tracker, LastIndex}` computes, from a tracker's configuration and progress map,
the configuration and progress map after a change, without touching the tracker (it copies it);
`Restore` replays a `ConfState`. Its users: raft's `applyConfChange` (`Simple`, `EnterJoint`,
`LeaveJoint`, by the change's transition: R2), `newRaft` and `appliedSnap` (`Restore` from
`MakeProgressTracker`'s empty tracker: R2), and clients that pre-check a change the way raft will
apply it (`examples/raft/kvreconf`, `kvdurable`: `Restore`, then the `Changer`). The pure transition
is `Model.lean`'s; the tracker's resources `tracker/Api.lean`'s.

## The shape, in words

A `Changer` method takes the tracker value's configuration (`configOwn`, at any share: only read)
and its progress map (`progressMapOwn`, whole: the copies the method makes share each peer's
`Inflights` ring with the tracker's `Progress`, so the rings move to the result), with `TrackerOk`.
It returns `changed (F m)`: for `F m = some m'` (`F` the model's `simple`, `enterJoint cs al`,
`leaveJoint`), no error, the new configuration (`configOwn` at `m'`, fresh maps) and a fresh
progress map at `m'` (`Tracker.Carried`: each peer's `Progress` the tracker's with its learner mark
updated, or a fresh one at `LastIndex`); for `none`, an error and the tracker's progress map back.
So a caller that panics on the error (raft) needs `F m = some m'`, and a caller that branches on it
(the examples' pre-check) learns which.

`ccsPts sl dq cs` is raftpb's `RaftPb.ccsPts` (a `[]*ConfChangeSingle` slice, the slice and each
single at `dq`, whose getters read `cs`; a definition, so splittable per element), re-exported here
(integration I2: was a provisional opaque of this batch).

## Internal vocabulary (the package's own proofs)

`ccState B cfg trk m`: the `Changer`'s working copy (`checkAndCopy`'s result, mutated by `apply`'s
helpers): the `Config` value `cfg`'s maps hold `m` (incoming allocated; outgoing and `LearnersNext`
`nil` iff empty; `AutoLeave` as `m`'s), the map `trk` tracks exactly `m`'s ids, each `Progress` a
copy of the tracker's (`B`) with its learner mark per `m`, or fresh at `B.li`; and it holds the
tracker's progress map `B.mp` with its `Progress` structs, and every ring of `B.pv` (shared with the
copies). Realization: those Goose points-to's, `ownMap`s and `inflightsOwn`s. Its two exits:
`ccState_done` (a valid `m`: the result's resources) and `ccState_abort` (the tracker's progress map
back).

## Requirement snippets

`examples/specreq/raftconf/confchange.go`: `ReqApplyLikeRaft` (a client's pre-check with the
`Changer` agrees with what raft's `applyConfChange` will do: no error exactly when raft will not
panic), `ReqRestoreEmpty` (an empty `ConfState` restores to the empty configuration),
`ReqRestoreRoundTrip` (a configuration's `ConfState` restores to it), `ReqLastVoter` (removing the
last voter is an error, not a panic), `ReqJointCycle` (enter a joint configuration, then leave it).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Model
public import Spec.go_etcd_io.raft.v3.tracker.Api
public import Spec.go_etcd_io.raft.v3.raftpb.Api
public import Spec.PkgInit.go_etcd_io.raft.v3.confchange

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical
open Tracker

-- raftpb's `[]*ConfChangeSingle` ownership (`RaftPb.ccsPts`).
export RaftPb (ccsPts)

/-- **The tracker a `Changer` works from** (internal): its progress map (location, `*Progress`
locations, values), and the changer's `LastIndex` and the tracker's ring capacities. -/
structure Base where
  mp : GoMap
  prs : GMap w64 Loc
  pv : GMap w64 ProgressV
  li : w64
  mi : w64
  mb : w64

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]


/-- **The `Changer` `chg` works from tracker progress map `B`** (its tracker's map, `LastIndex`,
ring capacities), whose capacity is one a new peer's ring can have (`NewInflights`' bound). -/
def BaseOf (chg : go_etcd_io.raft.v3.confchange.Changer) (B : Base) : Prop :=
  chg.Tracker'.Progress' = B.mp ∧ chg.LastIndex' = B.li ∧ chg.Tracker'.MaxInflight' = B.mi ∧
    chg.Tracker'.MaxInflightBytes' = B.mb ∧ 0 ≤ sint.Z B.mi ∧ sint.Z B.mi ≤ inflightsMax

/-- **The new configuration and progress map** `(cfg, trk)` at `m'`, carried from `B`. -/
def resultOk (B : Base) (m' : Membership) (cfg : go_etcd_io.raft.v3.tracker.Config)
    (trk : GoMap) : IProp GF :=
  iprop(configOwn cfg (DFrac.own 1) m' ∗
    ∃ prs' pv', progressMapOwn trk prs' pv' ∗ ⌜Carried B.pv m' B.li B.mi B.mb pv'⌝)

/-- **A `Changer` method's result** (`(cfg, trk, err)`) for the model's answer `r`, from the
tracker progress map `B`: no error and the new configuration and progress map; or an error, and
`B`'s progress map back. -/
def changed (B : Base) (r : Option Membership) (cfg : go_etcd_io.raft.v3.tracker.Config)
    (trk : GoMap) (err : GoInterface) : IProp GF :=
  match r with
  | some m' => iprop(⌜err = interface.nil⌝ ∗ resultOk B m' cfg trk)
  | none => iprop(⌜err ≠ interface.nil⌝ ∗ progressMapOwn B.mp B.prs B.pv)

/-- **`Restore`'s and `chain`'s result**: as `changed`, but an error gives nothing back (the ops
before the failing one consumed the tracker's map). -/
def result (B : Base) (r : Option Membership) (cfg : go_etcd_io.raft.v3.tracker.Config)
    (trk : GoMap) (err : GoInterface) : IProp GF :=
  match r with
  | some m' => iprop(⌜err = interface.nil⌝ ∗ resultOk B m' cfg trk)
  | none => iprop(⌜err ≠ interface.nil⌝)

/-- (internal) **The `Changer`'s working copy**: `cfg` and `trk` hold `m`, from the tracker `B`. -/
opaque ccState (B : Base) (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap)
    (m : Membership) : IProp GF := iprop(True)

/-- (internal) The working copy behind a `*Config` (what `apply`'s helpers mutate). -/
def ccWork (B : Base) (cfgp : Loc) (trk : GoMap) (m : Membership) : IProp GF :=
  iprop(∃ cfg, typedPointsto cfgp cfg (DFrac.own 1) ∗ ccState B cfg trk m)

/-- (internal) A `chain` op `f`, run once: a changer transition with model `F` (a `func(Changer)
(Config, ProgressMap, error)`): from a valid configuration `m`, `changed B (F m)`, with the frame
`R` (what the closure reads when it runs: `Restore`'s `ConfState` and changes) taken and given back.
Not persistent: `chain` calls each op exactly once. -/
def opSpec (f : GoFunc) (F : Membership → Option Membership) (R : IProp GF) : IProp GF :=
  iprop(∀ (chg : go_etcd_io.raft.v3.confchange.Changer) (dq : DFrac) (m : Membership)
      (B : Base) (Φ : val → IProp GF),
    R ∗ configOwn chg.Tracker'.Config' dq m ∗ progressMapOwn B.mp B.prs B.pv ∗
      ⌜BaseOf chg B ∧ TrackerOk m B.pv ∧ m.Valid⌝ -∗
    ▷ (∀ cfg trk err, R ∗ configOwn chg.Tracker'.Config' dq m ∗ changed B (F m) cfg trk err -∗
        Φ (PairV (PairV #cfg #trk) #err)) -∗
    WP (App (Val #f) (Val #chg)) {{ Φ }})

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-! ### The model (pure) -/

/-- **A change keeps a configuration valid.** -/
def changeV2_valid.spec : Prop :=
  ∀ (c : V2) (m m' : Membership), m.Valid → changeV2 c m = some m' → m'.Valid

/-- Each `Changer` transition keeps a configuration valid (`Restore`'s steps, the pre-checks). -/
def transitions_valid.spec : Prop :=
  (∀ cs (m m' : Membership), m.Valid → simple cs m = some m' → m'.Valid) ∧
  (∀ al cs (m m' : Membership), m.Valid → enterJoint al cs m = some m' → m'.Valid) ∧
  (∀ (m m' : Membership), m.Valid → leaveJoint m = some m' → m'.Valid)

/-- **A change moves the voters one step** (`Quorum.Adjacent`: joint consensus, or one voter at a
time), from a configuration with voters (the bootstrap's first voter is the exception). With the
two incoming voter sets below `2^63` in all, so that `Simple`'s `int` count does not wrap. What R2's
quorum-intersection argument across configurations rests on. -/
def changeV2_adjacent.spec : Prop :=
  ∀ (c : V2) (m m' : Membership), m.Valid → m.voters ≠ ∅ → changeV2 c m = some m' →
    GMap.size m.voters + GMap.size m'.voters < 2 ^ 63 →
    Quorum.Adjacent m.voters m.votersOutgoing m'.voters m'.votersOutgoing

/-- **A legacy change** (`ConfChange.AsV2()`: one change, transition `Auto`) at any valid
configuration that is not joint (etcd's; the bootstrap's `AddNode`s from the empty one): the change
(`applyOne`: node `0` and `UpdateNode` change nothing, `AddNode` makes a voter, `AddLearnerNode` a
learner, `RemoveNode` removes, an unknown type is an error), then an error if no voter is left.
(R1's `Membership.applyChange_v1`, corrected: at the empty configuration even a no-op is the error
"removed all voters"; an unknown type is an error, not a removal.) -/
def changeV2_single.spec : Prop :=
  ∀ (c : Single) (m : Membership), m.Valid → m.votersOutgoing = ∅ →
    changeV2 ⟨TransitionAuto, [c]⟩ m =
      (applyOne c m).bind (fun m' => if m'.voters = ∅ then none else some m')

/-- **`Restore` gives back the configuration a `ConfState` lists**, from the empty tracker (raft's
`newRaft` and `appliedSnap`, the examples' pre-check). -/
def restore_lists.spec : Prop :=
  ∀ (m : Membership) (vs ls os ns : List w64) (al : Bool), m.Valid → Lists vs ls os ns al m →
    restore Membership.empty vs ls os ns al = some m

/-- `Restore`'s result is valid. -/
def restore_valid.spec : Prop :=
  ∀ (m0 m : Membership) (vs ls os ns : List w64) (al : Bool), m0.Valid →
    restore m0 vs ls os ns al = some m → m.Valid

/-- A configuration of voters only (no id `0`) is valid; so is the empty one. -/
def simple_valid.spec : Prop :=
  ∀ (vs : GSet w64), W64 0 ∉ vs → (Membership.simple vs).Valid

/-! ### The internal working copy -/

/-- A valid working copy is the method's result. -/
def ccState_done.spec : Prop :=
  ∀ (B : Base) cfg trk (m : Membership), m.Valid →
    ccState (GF := GF) B cfg trk m ⊢ resultOk B m cfg trk

/-- An abandoned working copy gives the tracker's progress map back. -/
def ccState_abort.spec : Prop :=
  ∀ (B : Base) cfg trk (m : Membership),
    ccState (GF := GF) B cfg trk m ⊢ progressMapOwn B.mp B.prs B.pv


end laws

end ConfChange
end EtcdGrove
end Perennial
