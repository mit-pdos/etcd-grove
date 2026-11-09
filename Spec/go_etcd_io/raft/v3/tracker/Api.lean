/-
# raft's `tracker` package (batch R4): resources and laws

The leader's view of the cluster: the configuration (`tracker.Config`), each peer's `Progress`
(match and next index, its replication state, its `Inflights` ring), and the votes of an election
(`ProgressTracker`). The pure model is `Model.lean`.

## The shape, in words

- **`configOwn cfg dq m`** (opaque): a `tracker.Config` value `cfg` whose four maps hold the
  configuration `m` at `dq`, in the canonical form every tracker raft builds keeps (the incoming
  map allocated; the outgoing map and `LearnersNext` `nil` when empty, as `checkInvariants`
  demands), and `m` is `Valid`. raft never writes a configuration's maps (confchange copies them),
  so any fraction serves its readers. Opened by `configOwn_open` to the `JointConfig` (quorum's
  `jointConfigOwn`, which raft reads and indexes directly) and the auto-leave flag.
- **`inflightsOwn p I`** (opaque): an `*Inflights` ring at `p` holding the value `I` (a capacity of
  at most `2^62` messages, `inflightsMax`: the ring's index arithmetic does not wrap below it; in
  Go the ring could not be allocated beyond it).
- **`progressOwn pr P`** (transparent): a `*Progress` at `pr` holding `P`, its ring owned. The
  `Progress` fields are the package's API (raft reads and writes `Match`, `Next`, `State`,
  `RecentActive`, `MsgAppFlowPaused`, `PendingSnapshot`, `IsLearner` directly, and overwrites a
  whole `Progress` in `reset`), so the struct points-to is visible; only the ring is opaque.
  `progressValOwn pv P` is the same for a `Progress` value (`getProgressCopy`'s, `Status`'s).
- **`progressMapOwn mp prs pv`**: a `ProgressMap` at `mp` mapping each id to its `*Progress`
  (`prs`), each holding `pv`'s value.
- **`trackerOwn tv T`**: a `ProgressTracker` value `tv` at the model `T` (configuration, progress
  map, votes, ring capacities) with `TrackerOk` (the progress map tracks exactly the configuration's
  ids, learners marked); `progressTracker t T`: the same at location `t` (raft's `r.trk`).
  Transparent, over the opaque pieces above, so that raft's direct field accesses (`r.trk.Progress`,
  `r.trk.Config = cfg`, `r.trk = MakeProgressTracker(...)`) are Goose struct accesses.

## Intended realization

`configOwn cfg dq m`: `jointConfigOwn cfg.Voters' dq m.voters m.votersOutgoing` with the incoming
half a map (not `nil`) and the outgoing `nil` iff empty, `majorityOwn cfg.Learners' dq m.learners`,
`majorityOwn cfg.LearnersNext' dq m.learnersNext` with `nil` iff empty, `cfg.AutoLeave' =
m.autoLeave`, `⌜m.Valid⌝`. `inflightsOwn p I`: `p ↦ iv` with `iv.buffer ↦* buf` (and its capacity),
`I.items` the ring's `count` entries from `start` (wrapping at `size`), `iv.bytes = I.bytes`, `start
< len(buf) ≤ size` (or `count = 0`, `start = 0`), `0 ≤ size ≤ 2^62`.

## Requirement snippets

`examples/specreq/raftconf/tracker.go`: `ReqCommittedQuorum` (`Committed()` is acknowledged by a
quorum), `ReqTallyVotes` (won only with a quorum of granted votes), `ReqVisitSorted` (`Visit`
visits every tracked id once, in increasing order, and may write the visited `Progress`),
`ReqInflightsFull` (`Add` below capacity, `Full` at it, `FreeLE` frees), `ReqProgressFlow` (the
probe/replicate/snapshot transitions raft makes), `ReqCloneFresh` (`Config.Clone` shares no map).
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Model
public import Spec.go_etcd_io.raft.v3.quorum.Api
public import Spec.PkgInit.go_etcd_io.raft.v3.tracker

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

/-! ## Pure helpers over the model -/

/-- The bound below which an `Inflights` ring's index arithmetic does not wrap (its capacity, an
`int`): the model's, since Go could not allocate a ring that large. -/
@[word_unfold] def inflightsMax : Nat := 2 ^ 62

/-- Each peer's match index (`0` for one not tracked): what `Committed()` counts. -/
def matchOf (pv : GMap w64 ProgressV) (v : w64) : w64 := ((pv !! v).map (·.matched)).getD (W64 0)

/-- The tracked voters recently active (`QuorumActive`'s votes). -/
def activeIds (pv : GMap w64 ProgressV) : GSet w64 :=
  domSet (GMap.filter (fun _ P => !P.isLearner && P.recentActive) pv)

/-- `TallyVotes`' counts: the tracked non-learners that voted `b`. -/
def tallyCount (pv : GMap w64 ProgressV) (votes : GMap w64 Bool) (b : Bool) : Nat :=
  GMap.size (GMap.filter (fun id P => !P.isLearner && decide (votes !! id = some b)) pv)

/-- The configuration's voter quorums: `q` holds a majority of each half. -/
def Membership.quorum (m : Membership) (q : GSet w64) : Prop :=
  Quorum.JointQ m.voters m.votersOutgoing q

/-- The Go value of a `Progress` holding `P` with its ring at `ins`. -/
def ProgressV.toGo [GooseExts] (P : ProgressV) (ins : Loc) : go_etcd_io.raft.v3.tracker.Progress :=
  ⟨P.matched, P.next, P.sentCommit, P.state.code, P.pendingSnapshot, P.recentActive, P.paused,
    ins, P.isLearner⟩

/-- **A tracker as a value**: configuration, progress map (locations and values), votes, ring
capacities. -/
structure TrackerV where
  conf : Membership
  prs : GMap w64 Loc
  pv : GMap w64 ProgressV
  votes : GMap w64 Bool
  maxInflight : w64
  maxBytes : w64

/-! ## Go ownership -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **A `Config` value `cfg` holding configuration `m`** (its maps at `dq`, canonical; `m`
valid). -/
opaque configOwn (cfg : go_etcd_io.raft.v3.tracker.Config) (dq : DFrac) (m : Membership) :
    IProp GF := iprop(True)

/-- **An `*Inflights` ring at `p` holding `I`**. Exclusive. -/
opaque inflightsOwn (p : Loc) (I : InflightsV) : IProp GF := iprop(True)

/-- A `Progress` value holding `P`, its ring owned. -/
def progressValOwn (pv : go_etcd_io.raft.v3.tracker.Progress) (P : ProgressV) : IProp GF :=
  iprop(⌜pv = P.toGo pv.Inflights'⌝ ∗ inflightsOwn pv.Inflights' P.ins)

/-- **A `*Progress` at `pr` holding `P`**. -/
def progressOwn (pr : Loc) (P : ProgressV) : IProp GF :=
  iprop(∃ pv, typedPointsto pr pv (DFrac.own 1) ∗ progressValOwn pv P)

/-- **A `ProgressMap` at `mp`**: id to `*Progress` (`prs`), each holding `pv`'s value. -/
def progressMapOwn (mp : GoMap) (prs : GMap w64 Loc) (pv : GMap w64 ProgressV) : IProp GF :=
  iprop(ownMap mp (DFrac.own 1) prs ∗ [∗map] _id ↦ pr;P ∈ prs;pv, progressOwn pr P)

/-- **A `ProgressTracker` value `tv` at `T`**. -/
def trackerOwn (tv : go_etcd_io.raft.v3.tracker.ProgressTracker) (T : TrackerV) : IProp GF :=
  iprop(configOwn tv.Config' (DFrac.own 1) T.conf ∗ progressMapOwn tv.Progress' T.prs T.pv ∗
    ownMap tv.Votes' (DFrac.own 1) T.votes ∗
    ⌜tv.MaxInflight' = T.maxInflight ∧ tv.MaxInflightBytes' = T.maxBytes ∧ TrackerOk T.conf T.pv⌝)

/-- **The `ProgressTracker` at `t` (raft's `r.trk`) at `T`**. -/
def progressTracker (t : Loc) (T : TrackerV) : IProp GF :=
  iprop(∃ tv, typedPointsto t tv (DFrac.own 1) ∗ trackerOwn tv T)

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- A configuration raft holds is valid. -/
def configOwn_valid.spec : Prop :=
  ∀ cfg dq (m : Membership), configOwn (GF := GF) cfg dq m ⊢ iprop(⌜m.Valid⌝)

/-- **What raft reads of a configuration directly**: its voters (`r.trk.Voters`, indexed, measured,
passed to quorum) and its auto-leave flag; closed again unchanged. -/
def configOwn_open.spec : Prop :=
  ∀ cfg dq (m : Membership), configOwn (GF := GF) cfg dq m ⊢
    Quorum.jointConfigOwn cfg.Voters' dq m.voters m.votersOutgoing ∗
    ⌜cfg.AutoLeave' = m.autoLeave⌝ ∗
    (Quorum.jointConfigOwn cfg.Voters' dq m.voters m.votersOutgoing -∗ configOwn cfg dq m)

/-- A configuration's maps are only read: shares of one combine. -/
def configOwn_fractional.spec : Prop :=
  ∀ cfg (m : Membership) (dq1 dq2 : DFrac),
    configOwn (GF := GF) cfg (dq1 • dq2) m ⊣⊢ configOwn cfg dq1 m ∗ configOwn cfg dq2 m

def inflightsOwn_timeless.spec : Prop := ∀ p I, Timeless (inflightsOwn (GF := GF) p I)

def configOwn_timeless.spec : Prop := ∀ cfg dq m, Timeless (configOwn (GF := GF) cfg dq m)

/-- An owned ring's capacity is below `inflightsMax`. -/
def inflightsOwn_size.spec : Prop :=
  ∀ p (I : InflightsV), inflightsOwn (GF := GF) p I ⊢
    iprop(⌜0 ≤ sint.Z I.size ∧ sint.Z I.size ≤ inflightsMax⌝)

end laws

end Tracker
end EtcdGrove
end Perennial
