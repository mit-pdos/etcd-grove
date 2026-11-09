/-
# raft's `quorum` package (batch R4): majorities, joint majorities, votes and quorum indices

`quorum` is pure computation over voter sets (`MajorityConfig` is a `map[uint64]struct{}`,
`JointConfig` two of them): who wins a vote, and which log index a quorum has acknowledged. Its
callers are raft's tracker (`ProgressTracker.Committed`, `TallyVotes`, `QuorumActive`: R4's
`tracker`), the read-index queue (`readOnly.maybeAdvance`: R3) and, through them, raft's safety
argument (R2), which rests on the **intersection** of quorums: two quorums of one joint
configuration, or of two configurations one change apart, share a voter (`jointQ_intersect`).

## The model (pure, transparent)

- `MajQ s q`: `q` holds a strict majority of the voters `s` (every set does, of the empty
  configuration: Go's convention, "elections on an empty config win"); `JointQ s0 s1 q`: of both
  halves. `granted votes`, `rejected votes`: the ids voting yes, no.
- `majVote s votes`, `jointVote s0 s1 votes`: `VoteResult` as Go computes it (`VoteWon` iff the
  granted votes are a quorum; `VoteLost` iff the voters that have not rejected are not).
- `MajorityIdx s f N`, `JointIdx s0 s1 f N`: `CommittedIndex` (`N` is the largest index a strict
  majority acknowledged, `f v` voter `v`'s acknowledgement; `2^64-1` for no voters; the smaller of
  the halves'). Stated as relations (unique `N`), exactly R3's (`ApiLog.lean`'s provisional
  `MajorityIdx`/`JointIdx`, which these replace).
- `Adjacent a0 a1 b0 b1`: two joint configurations one step apart (a non-empty half of one and of
  the other differ by at most one voter): what confchange's transitions keep (R4's
  `ConfChange.changeV2_adjacent`).

## Go ownership (transparent: the Go types themselves)

- `majorityOwn m dq s`: a `MajorityConfig` value `m` (a Go map, possibly `nil`) holding the set
  `s` (`ownMap` at `dq`). Transparent: a `MajorityConfig` *is* a Go set; raft indexes and
  measures the tracker's halves directly (`r.trk.Voters[0][r.id]`, `len(r.trk.Voters[1])`), with
  Perennial's map specs.
- `jointConfigOwn c dq s0 s1`: a `JointConfig` value, its halves `s0` (incoming) and `s1`
  (outgoing). Replaces R3's provisional predicate of the same name and signature.
- `isAckedIndexer l P acked`: the `AckedIndexer` contract (a bundle of its one method, as
  Perennial's `isLocker`), with the caller's resource `P`: `AckedIndex(id)` gives `acked id`.
  Persistent. Realized for raft's `readOnly` by R3 (`readOnly.AckedIndex.spec`, `P = readOnly ro
  rs`, `acked = rs.acks`) and for the tracker's `matchAckIndexer` inside `ProgressTracker.Committed`.

## Requirement snippets

`examples/specreq/raftconf/quorum.go`: `ReqJointCommitted` (a joint quorum index is acknowledged
by a majority of each half), `ReqJointVote` (a joint vote is won only with both halves),
`ReqEmptyHalf` (an empty half does not constrain).

## Limitation kept local

`CommittedIndex` sorts the acknowledged indices with `slices.Sort`, whose Perennial spec takes at
most `2^62` elements (`sortMax`): a bound no Go program needs, kept as a premise of the two
`CommittedIndex` specs only (PRINCIPLES, "Keep a tool's temporary limitation as local as possible").
-/
module

public import GeneratedProof.go_etcd_io.raft.v3.quorum
public import Spec.PkgInit.go_etcd_io.raft.v3.quorum

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Quorum

open Iris Iris.BI
open Classical

/-! ## The model -/

/-- `VoteResult`'s values. -/
def VotePending : w8 := W8 1
def VoteLost : w8 := W8 2
def VoteWon : w8 := W8 3

/-- Perennial's `slices.Sort` spec bound (at most `2^62` elements): a tool limitation, not Go's. -/
@[word_unfold] def sortMax : Nat := 2 ^ 62

/-- **`q` holds a strict majority of `s`** (every set does, of the empty `s`). -/
def MajQ (s q : GSet w64) : Prop :=
  s = ∅ ∨ GMap.size s < 2 * GMap.size (s ∩ q)

/-- `q` holds a majority of both halves. -/
def JointQ (s0 s1 q : GSet w64) : Prop := MajQ s0 q ∧ MajQ s1 q

/-- The ids that voted yes. -/
def granted (votes : GMap w64 Bool) : GSet w64 := domSet (GMap.filter (fun _ v => v) votes)

/-- The ids that voted no. -/
def rejected (votes : GMap w64 Bool) : GSet w64 := domSet (GMap.filter (fun _ v => !v) votes)

/-- `MajorityConfig.VoteResult`: won with a majority of yes votes, lost when the voters that have
not said no are no majority, pending otherwise. -/
def majVote (s : GSet w64) (votes : GMap w64 Bool) : w8 :=
  if MajQ s (granted votes) then VoteWon
  else if MajQ s (s \ rejected votes) then VotePending
  else VoteLost

/-- `JointConfig.VoteResult`: the halves' agreed result; lost if either lost; else pending. -/
def jointVote (s0 s1 : GSet w64) (votes : GMap w64 Bool) : w8 :=
  let r0 := majVote s0 votes
  let r1 := majVote s1 votes
  if r0 = r1 then r0 else if r0 = VoteLost ∨ r1 = VoteLost then VoteLost else VotePending

/-- **A majority quorum's index** (`MajorityConfig.CommittedIndex`): the largest `N` that a strict
majority of the voters `s` acknowledged (`f v ≥ N`); `2^64 - 1` for no voters. -/
def MajorityIdx (s : GSet w64) (f : w64 → w64) (N : w64) : Prop :=
  let n := (elements s).length
  let cnt := fun (M : w64) =>
    ((elements s).filter (fun v => decide (uint.nat M ≤ uint.nat (f v)))).length
  (n = 0 ∧ N = W64 (2 ^ 64 - 1)) ∨
  (n ≠ 0 ∧ n < 2 * cnt N ∧ ∀ M : w64, uint.nat N < uint.nat M → ¬ n < 2 * cnt M)

/-- **A joint quorum's index** (`JointConfig.CommittedIndex`): the smaller of the halves'. -/
def JointIdx (s0 s1 : GSet w64) (f : w64 → w64) (N : w64) : Prop :=
  ∃ N0 N1, MajorityIdx s0 f N0 ∧ MajorityIdx s1 f N1 ∧
    N = (if uint.nat N0 < uint.nat N1 then N0 else N1)

/-- A set's members in increasing order (`MajorityConfig.Slice`; the tracker's `VoterNodes`,
`Visit`). -/
def sorted (s : GSet w64) : List w64 :=
  (elements s).mergeSort (fun a b => decide (uint.nat a ≤ uint.nat b))

/-- The voters of `s` that acknowledged `N` or more. -/
def ackedFrom (s : GSet w64) (f : w64 → w64) (N : w64) : GSet w64 :=
  GMap.filter (fun v _ => decide (uint.nat N ≤ uint.nat (f v))) s

/-- **Two joint configurations one step apart**: a non-empty half of the first and a non-empty
half of the second differ by at most one voter (the same configuration; entering a joint
configuration, whose outgoing half is the old incoming one; leaving it; a simple change of one
voter). -/
def Adjacent (a0 a1 b0 b1 : GSet w64) : Prop :=
  ∃ x y, (x = a0 ∨ x = a1) ∧ (y = b0 ∨ y = b1) ∧ x ≠ ∅ ∧ y ≠ ∅ ∧
    GMap.size (x \ y) + GMap.size (y \ x) ≤ 1

/-! ## Go ownership -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **A `MajorityConfig` value `m`** (a Go map or `nil`) holding the voter set `s`, at `dq`. -/
def majorityOwn (m : GoMap) (dq : DFrac) (s : GSet w64) : IProp GF :=
  iprop(⌜m = map.nil ∧ s = ∅⌝ ∨ ownMap m dq s)

/-- **A `JointConfig` value `c`**: its incoming half holds `s0`, its outgoing half `s1`. -/
def jointConfigOwn (c : go_etcd_io.raft.v3.quorum.JointConfig) (dq : DFrac) (s0 s1 : GSet w64) :
    IProp GF :=
  iprop(∃ m0 m1, ⌜c.arr = [m0, m1]⌝ ∗ majorityOwn m0 dq s0 ∗ majorityOwn m1 dq s1)

/-- **The `AckedIndexer` contract** of interface value `l`, with the caller's resource `P`:
`AckedIndex(id)` keeps `P` and answers `acked id` (found, with the index; or not found). -/
def isAckedIndexer (l : GoInterface) (P : IProp GF) (acked : w64 → Option w64) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜l = interface.ok i⌝ ∗
    □ ∀ (id : w64) (Φ : val → IProp GF),
      P -∗ ▷ (∀ (idx : w64) (ok : Bool),
          P ∗ ⌜(ok = true ∧ acked id = some idx) ∨ (ok = false ∧ acked id = none)⌝ -∗
          Φ (PairV #idx #ok)) -∗
      WP (App (Val #(methods i.ty go!"AckedIndex" i.v)) (Val #id)) {{ Φ }})

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

def isAckedIndexer_persistent.spec : Prop :=
  ∀ l (P : IProp GF) acked, Persistent (isAckedIndexer l P acked)

/-- **Majority intersection**: two majorities of a non-empty set share a member. -/
def majQ_intersect.spec : Prop :=
  ∀ (s q1 q2 : GSet w64), s ≠ ∅ → MajQ s q1 → MajQ s q2 → ∃ id, id ∈ s ∧ id ∈ q1 ∧ id ∈ q2

/-- **Joint quorum intersection across one step**: a quorum of a joint configuration and a quorum
of the same one, or of one a step away (`Adjacent`: confchange's transitions), share a voter. What
raft's election safety and commit safety rest on (R2's cluster invariant). -/
def jointQ_intersect.spec : Prop :=
  ∀ (a0 a1 b0 b1 q1 q2 : GSet w64), Adjacent a0 a1 b0 b1 →
    JointQ a0 a1 q1 → JointQ b0 b1 q2 → ∃ id, id ∈ q1 ∧ id ∈ q2

/-- **A quorum index is acknowledged by a majority**: the voters that acknowledged it are one. -/
def majorityIdx_quorum.spec : Prop :=
  ∀ (s : GSet w64) (f : w64 → w64) (N : w64), MajorityIdx s f N → MajQ s (ackedFrom s f N)

/-- **A joint quorum index is acknowledged by a joint quorum** (what `maybeCommit`'s safety and the
read index's confirmation use). -/
def jointIdx_quorum.spec : Prop :=
  ∀ (s0 s1 : GSet w64) (f : w64 → w64) (N : w64), JointIdx s0 s1 f N →
    JointQ s0 s1 (ackedFrom (s0 ∪ s1) f N)

/-- **A won joint vote is a joint quorum of granted votes**, and conversely (R2's election
safety at `TallyVotes`; CheckQuorum's step-down at `QuorumActive`). -/
def jointVote_won.spec : Prop :=
  ∀ (s0 s1 : GSet w64) (votes : GMap w64 Bool),
    jointVote s0 s1 votes = VoteWon ↔ JointQ s0 s1 (granted votes)

/-- **A joint vote is lost exactly when a half's voters that did not say no are no majority** (the
candidate can no longer win). -/
def jointVote_lost.spec : Prop :=
  ∀ (s0 s1 : GSet w64) (votes : GMap w64 Bool),
    jointVote s0 s1 votes = VoteLost ↔
      ¬ MajQ s0 (s0 \ rejected votes) ∨ ¬ MajQ s1 (s1 \ rejected votes)

/-- A non-empty majority's index is one of its voters' acknowledgements (so at most their
largest: R3's reslice bounds in `maybeAdvance`). -/
def majorityIdx_mem.spec : Prop :=
  ∀ (s : GSet w64) (f : w64 → w64) (N : w64), s ≠ ∅ → MajorityIdx s f N → ∃ v, v ∈ s ∧ f v = N

/-- A joint index with a non-empty half is one of the voters' acknowledgements. -/
def jointIdx_mem.spec : Prop :=
  ∀ (s0 s1 : GSet w64) (f : w64 → w64) (N : w64), s0 ∪ s1 ≠ ∅ → JointIdx s0 s1 f N →
    ∃ v, v ∈ s0 ∪ s1 ∧ f v = N

end laws

end Quorum
end EtcdGrove
end Perennial
