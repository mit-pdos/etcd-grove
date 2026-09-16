# What etcd raft actually does

Facts about the implementation under verification that turned out to be
different from what the proof assumed. Each one was discovered because a
proof asserted something else and could not be completed — so each is
*checked against the generated code*, not read off the Go source or inferred
from the paper.

Kept separately from [gotchas.md](gotchas.md) because these are facts about
**the artifact being verified**, not about the proof tooling. If you are about
to assume something about a raft function, look here first, then read its
translated body in `new/code/go_etcd_io/raft/`.

Started 2026-09-16.

## `appendEntry` is not a pure log operation

It updates the log **and queues a self-addressed `MsgAppResp` into
`r.msgsAfterAppend`**. A leader appending its own entry acknowledges it to
itself *by message*, not by updating the tracker directly.

That is also why `msgsAfterAppend` exists as a separate queue from `msgs`:
the self-ack must not reach the state machine before the append is durable.
`send` routes vote and append *responses* there and everything else to
`msgs`.

Cost: `wp_raft__appendEmptyEntry` was a false axiom (it owned only
`own_raftLog`) until 2026-09-15.

## A new leader's initial broadcast is not uniform

`bcastAppend` → `Visit` → `sendAppend` → `maybeSendAppend` does **not** send
one `MsgApp` per peer. Per peer it may:

- send nothing — the peer is paused (`pr.IsPaused()`), or
  `len(ents) == 0 && !sendIfEmpty`;
- send a **`MsgSnap`** instead — if `raftLog.term(prevIndex)` or
  `raftLog.entries(...)` errors, control falls through to
  `maybeSendSnapshot`. A follower whose log was compacted past its `Next`
  gets a snapshot, not an append;
- send nothing even then — `maybeSendSnapshot` returns `false` without
  sending if the peer is not `RecentActive`.

So what a follower receives depends on *that follower's* replication state.

Cost: `step_win` claimed one `App` per peer; weakened to `app_sends` on
2026-09-16. See [decisions.md](decisions.md).

## `send` panics rather than sending a malformed message

Two panics, both reachable from the election path, and both mean the path has
to be shown *unreachable* rather than assumed away — `wp_Logger__logf`
deliberately covers only the non-panicking `Logger` methods.

- `m.Term == 0` on a vote message → `Panicf("term should be set when sending
  %s")`. Term 0 is etcd raft's "unset". So term overflow at `2^64 - 1` in
  `campaign` (which sends at `r.Term` after `becomeCandidate` increments it)
  becomes a **panic**, not a silent wrap. Hence the no-wrap premise on
  `wp_raft__campaign_body`.
- A self-addressed non-response (`m.To == r.id` for a `MsgVote`) → panic.

The second explains a design detail worth knowing: **a candidate votes for
itself by injecting a `MsgVoteResp` into its own queue**, not by calling
`RecordVote`. See `campaign`'s `id == r.id` branch, which sends
`voteRespMsgType(voteMsg)` to itself and `continue`s.

## `r.step` is a function pointer, and it is briefly out of sync with the role

The `becomeX` functions swap `r.step` between `stepFollower`,
`stepCandidate` and `stepLeader`. `becomeFollower` assigns `r.step` **before**
`r.state`, and calls `reset` in between — so there is a window where the
pointer and the role disagree. Harmless single-threaded, but it is why
`own_raft_phys` had to be parameterized over the step function
(`own_raft_phys_at … f`) rather than tying `r.step` to the role
unconditionally.

A `MsgVoteResp` reaches `r.step(m)` through `Step`'s default arm, so the
pointer's value is load-bearing for that proof.

## `promotable()` has three conditions, not one

    pr := r.trk.Progress[r.id]
    return pr != nil && !pr.IsLearner && !r.raftLog.hasNextOrInProgressSnapshot()

The third is easy to miss: **a node refuses to campaign while it has a
pending or in-progress snapshot.** So `promotable` is not simply
"am I a voter".

Cost: `wp_raft__promotable`'s postcondition `b = bool_decide (id ∈ cfg)` is
not derivable without an `IsLearner = false` invariant (added to
`own_progress` on 2026-09-16) *and* the log, to discharge the snapshot check.

## `VoteLost` means "cannot still win", not "a majority rejected"

`MajorityConfig.VoteResult`:

    q = len(c)/2 + 1
    votedCnt >= q            -> VoteWon
    votedCnt + missing >= q  -> VotePending
    otherwise                -> VoteLost

So `VoteLost` fires when the candidate cannot reach a quorum *however the
remaining voters vote*. With 4 voters, 2 rejecting and 2 silent:
`votedCnt = 0`, `missing = 2`, `q = 3`, so `0 + 2 < 3` → `VoteLost`, while
the 2 rejections are **not** a quorum.

The identity worth remembering:

    votedCnt + missing = size cfg − size (rejected ∩ cfg) = size (cfg ∖ rejected)

so `VoteLost ⟺ ¬ is_quorum cfg (cfg ∖ rejected)`.

Cost: this was the most serious one — `stepCandidate` was already `Qed` and
consumed the false claim, so that proof was unsound. See
[decisions.md](decisions.md).

## `MajorityConfig.VoteResult` returns `VoteWon` for an empty config

`if len(c) == 0 { return VoteWon }`. That is why the joint-configuration
logic collapses to the first component when there is no reconfiguration: the
nil second half always reports `VoteWon`, so `JointConfig.VoteResult`'s
`r1 == r2` test or its `VoteLost` disjunct decides the outcome from `r1`
alone.

That convention has teeth. A spec saying `VoteResult = VoteWon → is_quorum
cfg (granted votes)` is **false** at `cfg = ∅`, because `is_quorum ∅ q`
unfolds to `0 < 2 * 0`. Discovered 2026-09-16, in exactly that form, in
`wp_ProgressTracker__TallyVotes`. `own_tracker` now carries `cfg ≠ ∅`.

## `ProgressTracker.Visit` sorts too, and it has a fast path

Same story as `campaign` below: `Visit` collects the progress-map keys and
`slices.Sort`s them, so the closure sees peers in ascending id order rather
than in Go's randomised map order. That is deliberate — it is what makes
`reset` deterministic.

The collection has a `var sl [7]uint64` stack buffer with
`if len(sl) >= n { ids = sl[:n] } else { ids = make([]uint64, n) }`. Seven is
not a magic property of raft; it is "big enough for most clusters, small
enough to stack-allocate". Both branches matter to a proof: the fast path is
taken whenever `size cfg <= 7`, which is every realistic cluster.

## `raftLog.lastIndex` and `raftLog.term` panic on a storage error

Neither returns the error. `lastIndex` calls `l.storage.LastIndex()` and
`panic(err)`s; `term` calls `l.storage.Term(i)`, passes `ErrCompacted` and
`ErrUnavailable` back to its caller, and `panic`s on anything else.
`lastEntryID` adds a third: it `Logger.Panicf`s if `term` fails at the index
`lastIndex` just returned.

So raft's *own* reading of the `Storage` contract is that these do not fail,
which is what makes it honest to state `is_Storage` with `#interface.nil`
error returns rather than an error-handling disjunction. A proof cannot dodge
it either way: `go.panic` does not return, and `wp_Logger__logf` deliberately
excludes `Panicf`, so each path has to be shown unreachable rather than
assumed away.

## A stale message is dropped silently, under our scope

`Step`'s `case m.Term < r.Term` looks busy — it can send a `MsgAppResp`, or
a rejecting `MsgPreVoteResp`, or handle a `MsgStorageAppendResp`. With
`checkQuorum` and `preVote` both off, **every one of those arms is guarded
off** for an election message: the first needs `checkQuorum || preVote`, the
second needs `MsgPreVote`, the third needs `MsgStorageAppendResp`. What runs
is the trailing `Infof` and `return nil`. So under our scope a stale
`MsgVote` or `MsgVoteResp` is simply logged and dropped.

## `hasUnappliedConfChanges` really does scan

    if r.raftLog.applied >= r.raftLog.committed { return false }
    ... scan (applied, committed] for EntryConfChange / EntryConfChangeV2 ...

The early return is guarded by `applied >= committed`, which is a fact about
the log that nothing in the election scope implies. So the scan is **not**
vacuous under "no reconfiguration": `hup` can genuinely refuse to campaign
because of *un-applied* configuration changes, and "the voter set is fixed"
does not rule that out.

Resolved 2026-09-16 by strengthening the scope assumption to **no
configuration change is ever requested** — so the log contains no
`EntryConfChange`/`EntryConfChangeV2` entry and the scan finds nothing. That
is a statement about the log's *contents*, so it belongs as a conjunct of
`own_raftLog`; the lemma stays `Admitted` until that predicate is real. The
distinction is worth keeping: a fixed voter set is about the resulting
configuration, whereas this is about what was ever appended.

## The five `traceX` functions are no-ops

`traceReceiveMessage`, `traceSendMessage`, `traceBecomeFollower`,
`traceBecomeCandidate`, `traceBecomeLeader` all translate to

    λ: <> <>, exception_do (do:  #())

Tracing is a disabled hook in this fork. They were `Axiom`s for days; each is
a two-line proof. **Six of the nineteen election-path axioms cost nothing but
reading the generated body.**

## `campaign` sorts the voter ids

It collects `r.trk.Config.Voters.IDs()` into a slice and calls
`slices.Sort` before iterating, so vote requests go out in ascending node-id
order. Not a correctness property — the model accepts any permutation — but
it is observable behaviour, and it is why `campaign` cannot be proved without
a `slices.Sort` spec (which Goose does not translate; see
[journal.md](journal.md)).
