/-
# raft's `tracker` package (batch R4): the pure model

What a configuration is (`Membership`, the meaning of a `tracker.Config`), which ones raft accepts
(`Membership.Valid`), and what the leader tracks of each peer (`ProgressV`, `InflightsV`: the
`Progress` struct and its `Inflights` ring as values). Transparent, no resources, no theorems: the
resources are `Api.lean`'s, what a change does to a configuration is confchange's
(`SpecPlan/Spec/go_etcd_io/raft/v3/confchange/Model.lean`).

**Shared with raft's node API (R1).** R1's `Model.lean` declared its own `Membership` (the same five
fields) and left `Membership.Valid` opaque for this batch; at integration R1's `structure
Membership` becomes `abbrev Membership := Tracker.Membership` (field names and helper definitions
`simple`, `empty`, `ids`, `isJoint` are the same), and its opaque `Valid` this definition. This
module imports nothing of raft's, so that R1's `Model.lean` can import it.
-/
module

public import GeneratedProof.go_etcd_io.raft.v3.tracker

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Classical

/-! ## Configurations -/

/-- **A configuration** (a `tracker.Config`): the incoming voters (`Voters[0]`), the outgoing
voters of a joint configuration (`Voters[1]`), the learners, the learners to be added when the
joint configuration is left (`LearnersNext`: outgoing voters being demoted), and whether the joint
configuration is left automatically. -/
structure Membership where
  voters : GSet w64
  votersOutgoing : GSet w64
  learners : GSet w64
  learnersNext : GSet w64
  autoLeave : Bool

/-- A configuration of voters only. -/
def Membership.simple (vs : GSet w64) : Membership := ⟨vs, ∅, ∅, ∅, false⟩

/-- The empty configuration (a node that knows of no member: `MakeProgressTracker`'s). -/
def Membership.empty : Membership := Membership.simple ∅

/-- Every id the configuration tracks (the domain of the tracker's progress map). -/
def Membership.ids (m : Membership) : GSet w64 :=
  m.voters ∪ m.votersOutgoing ∪ m.learners ∪ m.learnersNext

def Membership.isJoint (m : Membership) : Prop := m.votersOutgoing ≠ ∅

/-- **What `checkInvariants` accepts** of a configuration whose progress map tracks exactly its ids,
each `IsLearner` iff a learner (what every tracker raft builds keeps): staged learners are outgoing
voters; learners are no voters; a configuration that is not joint has no staged learner and no
auto-leave. (Go also asks the non-joint `Voters[1]` and `LearnersNext` to be `nil`, not just empty:
`Api.lean`'s `configOwn` keeps them so.) -/
def Membership.CfgOk (m : Membership) : Prop :=
  m.learnersNext ⊆ m.votersOutgoing ∧
  m.learners ∩ (m.voters ∪ m.votersOutgoing) = ∅ ∧
  (m.votersOutgoing = ∅ → m.learnersNext = ∅ ∧ m.autoLeave = false)

/-- **A configuration raft accepts and reaches**: `checkInvariants`' conditions; no id `0` (the id
confchange skips: etcd's refused change); voters unless the configuration is empty (confchange
refuses to remove the last voter, and a learner cannot be added to a voterless configuration); no
staged learner among the incoming voters (confchange never stages one). Exactly the configurations
`confchange.Restore` restores from a `ConfState` listing them (`ConfChange.restore_lists.spec`),
and kept by every change (`ConfChange.changeV2_valid.spec`). No size bound: the `2^62` of
Perennial's sort is a premise of the specs that sort (`Visit`, `VoterNodes`, `ConfState`,
`CommittedIndex`). -/
def Membership.Valid (m : Membership) : Prop :=
  m.CfgOk ∧ W64 0 ∉ m.ids ∧ (m.voters = ∅ → m.ids = ∅) ∧ m.learnersNext ∩ m.voters = ∅

/-! ## Progress -/

/-- A follower's replication state (`StateType`). -/
inductive PrState where
  | probe
  | replicate
  | snapshot
deriving DecidableEq

/-- Its Go value (`StateProbe = 0`, `StateReplicate = 1`, `StateSnapshot = 2`). -/
def PrState.code : PrState → w64
  | .probe => W64 0
  | .replicate => W64 1
  | .snapshot => W64 2

/-- **An `Inflights` ring** as a value: its capacity in messages (`size`, an `int`) and bytes
(`maxBytes`, `0` for none), and the messages in flight, oldest first, each `(index, bytes)`: the
last entry's index and the message's payload size. -/
structure InflightsV where
  size : w64
  maxBytes : w64
  items : List (w64 × w64)

/-- The bytes in flight, as Go keeps them (a `uint64` sum, wrapping). -/
def InflightsV.bytes (I : InflightsV) : w64 := W64 ((I.items.map (fun it => uint.nat it.2)).sum)

/-- `Full()`: as many messages as the capacity, or the byte budget (if any) reached. -/
def InflightsV.full (I : InflightsV) : Bool :=
  decide (I.items.length = sint.nat I.size) ||
    (decide (I.maxBytes ≠ W64 0) && decide (uint.nat I.maxBytes ≤ uint.nat I.bytes))

/-- `FreeLE(to)`: the messages up to `to` acknowledged (freed from the front, in order). -/
def InflightsV.freeLE (I : InflightsV) (to : w64) : InflightsV :=
  { I with items := I.items.dropWhile (fun it => decide (uint.nat it.1 ≤ uint.nat to)) }

/-- A new, empty ring (`NewInflights(size, maxBytes)`). -/
def InflightsV.empty (size maxBytes : w64) : InflightsV := ⟨size, maxBytes, []⟩

/-- **A `Progress` value** (what the leader tracks of a peer), its `Inflights` as a value. -/
structure ProgressV where
  matched : w64
  next : w64
  sentCommit : w64
  state : PrState
  pendingSnapshot : w64
  recentActive : Bool
  paused : Bool
  isLearner : Bool
  ins : InflightsV

/-- `IsPaused()`. -/
def ProgressV.isPaused (P : ProgressV) : Bool :=
  match P.state with
  | .probe => P.paused
  | .replicate => P.paused
  | .snapshot => true

/-- `ResetState(st)`: the flow unpaused, no pending snapshot, the ring emptied. -/
def ProgressV.resetState (P : ProgressV) (st : PrState) : ProgressV :=
  { P with paused := false, pendingSnapshot := W64 0, state := st, ins := { P.ins with items := [] } }

/-- `BecomeProbe()`. -/
def ProgressV.becomeProbe (P : ProgressV) : ProgressV :=
  let next := if P.state = .snapshot
    then (if uint.nat (P.matched + 1) < uint.nat (P.pendingSnapshot + 1) then P.pendingSnapshot + 1
          else P.matched + 1)
    else P.matched + 1
  let P1 := { P.resetState .probe with next := next }
  { P1 with sentCommit := if uint.nat P1.sentCommit < uint.nat (next - 1) then P1.sentCommit
                          else next - 1 }

/-- `BecomeReplicate()`. -/
def ProgressV.becomeReplicate (P : ProgressV) : ProgressV :=
  { P.resetState .replicate with next := P.matched + 1 }

/-- `BecomeSnapshot(i)`. -/
def ProgressV.becomeSnapshot (P : ProgressV) (i : w64) : ProgressV :=
  { P.resetState .snapshot with pendingSnapshot := i, next := i + 1, sentCommit := i }

/-- `SentEntries(n, bytes)` in probe or replicate (it panics in snapshot). -/
def ProgressV.sentEntries (P : ProgressV) (n : w64) (bytes : w64) : ProgressV :=
  match P.state with
  | .replicate =>
    let P1 := if 0 < sint.Z n
      then { P with next := P.next + n,
                    ins := { P.ins with items := P.ins.items ++ [(P.next + n - 1, bytes)] } }
      else P
    { P1 with paused := P1.ins.full }
  | _ => if 0 < sint.Z n then { P with paused := true } else P

/-- `CanBumpCommit(i)`. -/
def ProgressV.canBumpCommit (P : ProgressV) (i : w64) : Bool :=
  decide (uint.nat P.sentCommit < uint.nat i) && decide (uint.nat P.sentCommit < uint.nat (P.next - 1))

/-- `MaybeUpdate(n)`: the new value and whether it changed. -/
def ProgressV.maybeUpdate (P : ProgressV) (n : w64) : ProgressV × Bool :=
  if uint.nat n ≤ uint.nat P.matched then (P, false)
  else ({ P with matched := n,
                 next := if uint.nat P.next < uint.nat (n + 1) then n + 1 else P.next,
                 paused := false }, true)

/-- `MaybeDecrTo(rejected, hint)`: the new value and whether it changed. -/
def ProgressV.maybeDecrTo (P : ProgressV) (rej hint : w64) : ProgressV × Bool :=
  let minW := fun (a b : w64) => if uint.nat a < uint.nat b then a else b
  let maxW := fun (a b : w64) => if uint.nat a < uint.nat b then b else a
  if P.state = .replicate then
    if uint.nat rej ≤ uint.nat P.matched then (P, false)
    else let next := P.matched + 1
      ({ P with next := next, sentCommit := minW P.sentCommit (next - 1) }, true)
  else if P.next - 1 ≠ rej then (P, false)
  else let next := maxW (minW rej (hint + 1)) (P.matched + 1)
    ({ P with next := next, sentCommit := minW P.sentCommit (next - 1), paused := false }, true)

/-- **A new peer's `Progress`** (confchange's `initProgress`, at the changer's `LastIndex` `li`
and the tracker's ring capacities): nothing matched, probing from `max(li, 1)`, recently active. -/
def ProgressV.fresh (li : w64) (isLearner : Bool) (mi mb : w64) : ProgressV :=
  ⟨W64 0, (if li = W64 0 then W64 1 else li), W64 0, .probe, W64 0, true, false, isLearner,
    InflightsV.empty mi mb⟩

/-! ## A tracker's progress map against its configuration -/

/-- **The progress map fits the configuration** (what every tracker raft builds keeps): it tracks
exactly the configuration's ids, each marked a learner iff it is one. -/
def TrackerOk (m : Membership) (pv : GMap w64 ProgressV) : Prop :=
  domSet pv = m.ids ∧ ∀ id P, pv !! id = some P → P.isLearner = decide (id ∈ m.learners)

/-- **The progress map after a configuration change** (confchange's result, at changer
`LastIndex` `li` and ring capacities `mi`, `mb`): it fits the new configuration `m'`; each peer's
`Progress` is the old one with its learner mark updated, or a fresh one (always for a peer not
tracked before; also for one removed and re-added in the same change). -/
def Carried (pv : GMap w64 ProgressV) (m' : Membership) (li mi mb : w64)
    (pv' : GMap w64 ProgressV) : Prop :=
  TrackerOk m' pv' ∧ ∀ id P', pv' !! id = some P' →
    P' = ProgressV.fresh li (decide (id ∈ m'.learners)) mi mb ∨
    ∃ P, pv !! id = some P ∧ P' = { P with isLearner := decide (id ∈ m'.learners) }

end Tracker
end EtcdGrove
end Perennial
