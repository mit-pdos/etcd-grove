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

Cost: `wp_raft__appendEntry` — called `wp_raft__appendEmptyEntry` until
2026-09-18, after a Go method that does not exist — was a false axiom (it
owned only
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
`r.step` cannot be a function of the role in the abstract state: it is its
own field, `nstate.stepfn : func.t` (since 2026-09-22; before that a
variant predicate `own_raft_phys_at … f` carried it), and `nstate_wf`
says the two agree between top-level calls.

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
a two-line proof. Since 2026-09-23 their specs (and `traceReplicate`'s)
own nothing -- `{{{ is_pkg_init raft }}} … {{{ RET #(); True }}}` -- because
the body touches nothing; a build with tracing on would need specs on
`own_raft_phys`. **Six of the nineteen election-path axioms cost nothing but
reading the generated body.**

## `campaign` sorts the voter ids

It collects `r.trk.Config.Voters.IDs()` into a slice and calls
`slices.Sort` before iterating, so vote requests go out in ascending node-id
order. Not a correctness property — the model accepts any permutation — but
it is observable behaviour, and it is why `campaign` cannot be proved without
a `slices.Sort` spec (which Goose does not translate; see
[journal.md](journal.md)).

Where it came from: upstream commit `07c1ab6` ("raft/rafttest: introduce
datadriven testing", 2019) replaced `for id := range r.prs.Voters.IDs()`
with collect-then-sort in the same change that added the `testdata/*.txt`
interaction tests, which compare message order verbatim. The sort exists to
make those tests reproducible under Go's randomised map iteration; `065fbde`
later changed `sort.Slice` to `slices.Sort`. So the permutation-only
`wp_slices_Sort` is not losing anything the protocol needs.

## `raftLog.scan` pages by byte budget inside `slice`, not by index (2026-09-20)

`scan(lo, hi, pageSize, v)` calls `l.slice(lo, hi, pageSize)` with the
**whole remaining range** and `pageSize` as `maxSize`; the page is cut by
`limitSize` inside `slice`. So `scan` knows nothing about a page beyond
`slice`'s postcondition, and its progress bound `lo + len(ents) ≤ hi` is
exactly `length es ≤ hi - lo` there. That bound also rules out the `w64`
wrap in `lo += uint64(len(ents))`, so `own_raftLog_at`'s `Hnowrap` is not
needed by `scan`.

## `hasUnappliedConfChanges`'s callback writes only on the conf-change branch

Its only write is `found = true`, under `e.Type == EntryConfChange ||
EntryConfChangeV2`. Under the election scope (`HnoConfChange`) that branch
is dead, so the callback invariant can be `emp`. Structurally this matters:
`scan_closure` is demanded under `□`, so the closure cannot capture the
enclosing frame's `found_ptr ↦ false`; had the write been live, the pointer
would have had to be threaded through `I` the way `reset` threads
`r_ptr ↦ r` through `Visit`. `EntryNormal/EntryConfChange/EntryConfChangeV2`
are `W32 0/1/2` (raftpb.v), so `defs.v`'s `w32_ne` closes the comparisons.

## `appendEntry`, checked against the body (2026-09-20)

The reject path logs with `Warningf` (not a trace hook); `traceReplicate` is
`λ: <> <>, do: #()`; `raftLog.append` returns `lastIndex()` early for an
empty batch and its `Panicf` guard is `after < committed` with
`after = ents[0].Index - 1`; `payloadSize` takes the entry by value and
needs no ownership. The method writes only `Term` and `Index` into the
caller's entries, so the caller's `Type` lands in the log —
`wp_raft__appendEntry` therefore requires `Type = EntryNormal`, which
`becomeLeader`'s `pb.Entry{Data: nil}` satisfies as the zero value.

## The append-broadcast path, checked against the bodies (2026-09-20)

- `raftLog.slice` has **five** returning exits: the unstable-only slice
  (`ents[0:len:len]`) and four `return ents` from the storage path
  (`hi <= offset`, `len(ents) < cut-lo`, `size >= maxSize`, the
  `len(unstable)==1 && …` guard), plus `extend(ents, unstable)`, the only
  one that allocates. `min(hi, l.unstable.offset)` genuinely needs a case
  split: the arms give different `Storage.Entries` ranges.
- `limitSize` calls `Size()` on `&ents[0]` and `&ents[limit]` — the address,
  not a copy (`own_slice_elem_acc`). `unstable.slice` returns
  `u.entries[a:b:b]` (`cap = len`), which is what makes `extend` reallocate
  instead of writing into the suffix, matching `Storage.Entries`'s `cap = len`.
- `maybeSendAppend`'s fetch guard is `pr.State != StateReplicate ||
  !pr.Inflights.Full()` (Goose's `⟨go.bool⟩!` is negation) — in
  `StateReplicate` entries are fetched only when the window is not full,
  which is exactly `SentEntries`'s second premise. `reset`'s `Progress`
  literal omits `State`, so the zero value `StateProbe` is what
  `progress_state_ok` is established at.
- `Inflights.Add` panics on a full window and writes into a ring
  (`buffer[(start+count) mod size]`, growing on demand); `Progress.IsPaused`
  panics outside Probe/Replicate/Snapshot; `Progress.SentEntries` outside
  Probe/Replicate. `Storage.Snapshot`'s callers panic on any error other
  than `ErrSnapshotTemporarilyUnavailable` and on an empty snapshot.

## `Inflights.grow` allocates one slot past the ring when `size = 0` (2026-09-21)

`newSize := 2*len(buffer); if newSize == 0 { newSize = 1 } else if newSize > size
{ newSize = size }` — the cap at `size` is in the `else` arm, so with
`size = 0` (hence an empty buffer) it allocates one slot, breaking
`len(buffer) ≤ size`. `Add` never reaches `grow` in that state (`Full()` is
true at `size = 0`), so the `grow` triple carries `len(buf) < size` as a
premise and the call site discharges it. In `Add` itself, when the ring
wraps (`start + count ≥ size`) the buffer is already full-length, so the
"wrap and grow" case is unreachable.

## `raftLog.term` is total; the term it returns is not pinned (2026-09-21)

`term(i)` returns `(0, ErrCompacted)` for `i+1 < firstIndex`,
`(0, ErrUnavailable)` for `i > lastIndex`, and in range panics only on a
`Storage.Term` error, which `is_Storage`'s `HTerm` excludes. Its triple now
says `err = nil ↔ i in range` and nothing about the term value: in the
unstable part the value comes from `unstable.maybeTerm`, whose spec does
not pin it, and `term_at` covers only the stable prefix. The `i + 1` wrap at
`2^64 - 1` fires the `ErrCompacted` branch, consistent with `Hnowrap`. The
`←` half is what `maybeSendAppend` needs to call `entries(pr.Next, …)`
afterwards (`prev.index + 1 ≤ pr.Next`); the two named errors are not in the
postcondition because `is_initialized`'s globals are existential inside
`is_pkg_init raft` and no caller tests which error it is.

## `maybeSendSnapshot`, checked against the body (2026-09-21)

The `MsgSnap` literal has `To := to`, `Type := 7`, `From := 0`, `Term := 0`,
so `send_ok`'s third clause applies verbatim and the abstract outbox is
unchanged. Its `Snapshot` field is the **address of the local `snapshot`
variable**, not a copy: raft hands a pointer into the caller's frame to
`send`. Nothing in the current model observes it; a later `MsgSnap`-aware
model must not get it wrong. `raftLog.snapshot`'s unstable early return is
dead under `own_raftLog_at`'s `Hnosnap`, so every snapshot on the election
path comes from the client `Storage`. `Progress.BecomeSnapshot` keeps
`progress_state_ok` (`StateSnapshot = 2`).


## Which slices raft hands out uncapped (2026-09-29)

Checked against upamanyus/etcd-raft 531b20c, for the read-only-entries
change (decisions.md, 2026-09-29). **No log entry is ever written in
place**: `unstable.slice` caps its result (`log_unstable.go:233`),
`raftLog.slice` re-caps the unstable-only case (`log.go:508`),
`MemoryStorage.Entries` caps (`storage.go:155`), and truncation
reallocates through the capped `u.slice` (`log_unstable.go:212-213`). Five
places do hand out a slice aliasing internal state *without* capping it:

- `unstable.nextEntries`, `log_unstable.go:101`: `u.entries[inProgress:]`,
  which becomes `Ready.Entries` (`rawnode.go:145`). An application append
  reaches only the slack, but raft's next fast-path append
  (`log_unstable.go:201`) writes the same slack and would overwrite it.
- `readOnly.maybeAdvance`, `read_only.go:85`: returns
  `ro.unconfirmedReads[:k]` and keeps `unconfirmedReads[k:]`. **An append
  to the result would overwrite live pending reads.** Safe only by use:
  its one caller (`raft.go:1592`) just ranges over it.
- `Ready.Messages = r.msgs` (`rawnode.go:147`), `m.Responses =
  r.msgsAfterAppend` (`rawnode.go:257`), `rd.ReadStates = r.readStates`
  (`rawnode.go:161`): uncapped, but `acceptReady` sets each field to `nil`
  (`rawnode.go:413,433-434`), so the application ends up owning the array.

Conditional on the `Storage` contract: `raftLog.slice` returns
`Storage.Entries`' result without re-capping (`log.go:520-533`), and
`extend` appends in place into `cap(dst)` slack (`util.go:318-319`); both
are safe exactly when `cap = len`, which `is_Storage` demands. `limitSize`
(`util.go:276`) is uncapped but every caller re-caps. In the other
direction, `truncateAndAppend`'s `u.entries = ents` (`log_unstable.go:206`)
adopts the *caller's* slice, so a later fast-path append can write into
the caller's slack: a spec of that arm must take the batch's ownership
(today only the continuing arm is specified).
