# etcd-io/raft#47: raft: fix out-of-order terms

- PR: https://github.com/etcd-io/raft/pull/47 (open, needs rebase; changes requested by a
  reviewer), head `0b198cf121e5b32d9fb44bc4978d5d5750d28152`, against upstream `main` at merge base
  `ffef590a6`.
- Verified at the Goose fork commit `59be9c1e4` (branch `pr-raft-47-goose-lean`, worktree
  `~/etcd-pr/raft-47`): the pinned raft base `509271dac` (raft v3.7, protobuf-go v2) plus the PR.
- Lean branch `pr-verify/raft-47` (worktree `/shared/etcd-grove-pr/raft-47`).
- Go probes and logs: `notes/pr-verify/raft-47/` (README there).

## Verdict

The change is sound. Both new checks are proved dead in every state `raft.Step`'s spec covers, and
`raft.Step.spec` is unchanged. Everything above `Step` (RawNode, node, etcd's server) rebuilds
unchanged, and no axiom or `sorry` was added. So on every execution the model admits, the PR
changes nothing.

What the PR changes is behavior on states the model excludes:

- `appendEntry` panics when the log's last term is above the node's term, instead of appending
  entries out of order.
- `restore` refuses a snapshot of a later term and steps down to that term, instead of
  restoring it at the old term.

Such states come from a `Storage` whose `HardState.Term` is below its last entry's term, or from
messages no correct leader sends. The probes show the PR does what it says there. The first case
is an undocumented precondition of the existing code, now in
`issues/raft-storage-hardstate-term-below-log.md`.

Not covered:

- Restarts from a non-empty storage: `RestartNode.spec` starts from an empty one.
- The PR's test changes: they are ported and pass, but are not verified.

## Conflict resolution (verified code vs the PR)

`git apply -3` conflicted in `log.go` and `raft.go`. Resolved in the base's style:

- `log.go`: the PR's `tip() (index, term)` and its rewrite of `lastTerm()` are dropped. The base
  has no `lastTerm()` and already has `lastEntryID() entryID`, the same pair. The base's
  `lastEntryID` panic message is kept.
- `raft.go` `appendEntry`: `li, lt := r.raftLog.tip()` became `last := r.raftLog.lastEntryID();
  … li := last.index`, with the same check and message. The base's clone-and-stamp loop
  (`[]*pb.Entry`) is unchanged.
- `raft.go` `restore`: applied cleanly, but `s.Metadata.Term` became `s.GetMetadata().GetTerm()`
  (protobuf-go v2).
- Tests: ported to protobuf-go v2 messages.
  - `TestHandleHeartbeatResp`'s `SetHardState` takes a `*pb.HardState`.
  - `TestRestoreFromSnapMsg` uses `Term: new(uint64(11))`.
  - Two base tests the PR does not touch set up a log of terms 1, 2, 3 and then call
    `becomeCandidate`: `TestLeaderIncreaseNext` and `TestRecvMsgUnreachable`. (At the PR's base
    these logs were terms 1, 1, 1.) They now hit the new panic, so they first call
    `becomeFollower(3, None)`, as the PR does for its other tests.

`go build ./...`, `go vet .` and `go test ./...` pass in the fork worktree. The fork commit is not
pushed, so `etc/goose.py --check` fails on this branch, as expected. The translation differs only
in `appendEntry` and `restore`.

## Changed functions

Package `go.etcd.io/raft/v3`, `raft.go`, compared by `go/ast`. No type, field or package
variable changed.

| Function | Kind | Before (`lean`) | After | Outcome |
|---|---|---|---|---|
| `raft.appendEntry` | behavior change (new panic) | verified | verified | new spec, incompatible (stronger premise); callers checked |
| `raft.restore` | behavior change (new exit) | verified | verified | new spec, incompatible (new exit); the old statement plus a premise derived; callers checked |
| `raftLog.tip` / `raftLog.lastTerm` (upstream only) | new / changed | — | — | not in the port (see above) |

### `appendEntry`

- **Old spec**: for any state, the batch is stamped and appended (or dropped) and the
  self-acknowledgement is queued.
- **New spec**: the same, with the premise `LastTermLe s`: the last entry's term is at most
  `s.term`. The proof reads `lastEntryID()` and the `Panicf` branch is dead.
- Files: `Spec/go_etcd_io/raft/v3/raft__appendEntry.lean` (`LastTermLe`, `raft.appendEntry.spec`);
  `Proof/go_etcd_io/raft/v3/raft__appendEntry.lean`.
- The old spec does not hold of the new code. `ownRaftPhys` alone admits a log ahead of the term
  (`raft.Step.spec`'s pre-vote premise says so), and there the code now panics.

### `restore`

- **Old spec**: `RestoreResult`, three exits:
  1. obsolete: `false`, state unchanged;
  2. fast-forward: `false`, commit moved;
  3. restored: `true`.
- **New spec**: `RestoreResultG`, with a step-down exit:
  - When the snapshot is past the commit index and `s.term < snapshot term`, the result is
    `false` with `s' = becomeFollower s sterm 0` and the configuration unchanged.
  - Otherwise ("obsolete, or snapshot term ≤ s.term") `RestoreResult` holds as before. This
    reproduces Go's order of checks: obsolete index, role, term, `found`, `matchTerm`.
- `raft.restore.specT` is the old statement plus the premise `sv.Metadata.Term ≤ s.term`. It is
  derived from the new spec (`raft.restore.specT_of_spec`).
- Files: `Spec/go_etcd_io/raft/v3/raft__restore.lean`; `Proof/go_etcd_io/raft/v3/raft__restore.lean`,
  which gains the callee `becomeFollower`.
- Neither spec holds of the other version of the code:
  - without the check, a snapshot of a later term is restored, which `RestoreResultG` excludes;
  - with it, such a snapshot changes the term and returns `false`, which `RestoreResult` excludes.

## Callers (step 6)

Every caller is in raft and is reached only through `raft.Step`. This was checked by grep over the
fork and in `etc/link-lean-first-raft.txt`: `campaign` in v3.7 wins through its own
`MsgVoteResp`, so it never calls `becomeLeader`. The premises were threaded up to `Step`, whose
spec is unchanged:

```
appendEntry   (+ LastTermLe s)
├── becomeLeader                 (+ LastTermLe s)                                 proved
│   └── stepCandidate            (MsgVoteResp → LastTermLe s, in its term clause)  proved
│       └── raft.Step            discharged from the ghost state (TermsLe)         proved, spec unchanged
└── stepLeader                   (MsgProp clause + LastTermLe s)                   proved
    └── raft.Step                discharged from the ghost state                   proved, spec unchanged
restore       (new exit; specT = old + snapshot term ≤ term)
└── handleSnapshot               (+ snapshot term ≤ s.term; uses specT)           proved, result unchanged
    ├── stepFollower             (MsgSnap clause + the bound)                     proved
    └── stepCandidate            (MsgSnap clause + the bound; at the post-becomeFollower state)  proved
        └── raft.Step            discharged from isMessage (absSnap …)            proved, spec unchanged
```

The two facts come from the ghost state (`Proof/go_etcd_io/raft/v3/raft__Step/TermLe.lean`):

- `ownRaftGhost_lastTerm_le`: no term in a node's full log is above its own. This is `TermsLe`, a
  conjunct of `ownLogGhost` (`Protocol/GhostState.lean`).
- `isMessage_snap_term_le`, through `isMessage_absSnap_term_le`: a snapshot message's sender has
  the snapshot's last entry in its log, and no term in a leader's full log is above its own
  (`lpfull`).

At a `MsgSnap` of a higher term, `Step` first steps down to `m.Term`, so the bound is at the right
state.

The `Step` branch lemmas changed:

- they take the new facts as premises: `MsgVoteResp`, `MsgProp`, `MsgSnap`, `MsgSnap_eq`,
  `MsgSnap_gt`;
- they discharge the new conjunct of `stepCandidate`'s term clause trivially: `MsgApp_eq`,
  `MsgHeartbeat_eq`, `MsgAppResp_eq`, `MsgHeartbeatResp_eq`.

## Trust base (step 7)

No axiom or `sorry` was added. The new lemmas are proved from the existing ghost state. The only
new callee edge, `restore → becomeFollower`, is a proved function.

`etc/tcb-collections/pr-raft-47.txt` holds the roots `appendEntry`, `restore`, `handleSnapshot`,
`becomeLeader`, `stepCandidate`, `stepFollower`, `stepLeader` and `raft.Step`. Run on a full
`lake build` of the branch, they rest on 10 axioms and no `sorry`:

- `DescribeConfChange`, `fmt.Errorf`, `raftpb.ConfChangeType.String`;
- `proto.CloneConfState`, `CloneEntry`, `CloneSnapshot`, `EqualConfState`, `SizeEntry`,
  `UnmarshalConfChange`, `UnmarshalConfChangeV2`.

All of these are among the `raft` collection's existing trust-boundary axioms. Every other check
matches its baseline unchanged:

- `etc/tcb-report.py --check`: 229 axioms, 12 `sorry`s, the same as `lean`;
- the `raft` collection (13 axioms, 0 `sorry`s);
- the `server-raft` collection (6 axioms).

`etc/verified-code.py --package go.etcd.io/raft/v3`: `appendEntry` and `restore` are "verified
(sorry-free)" before and after. The package's counts are unchanged at 260 of 327 functions
verified.

## Findings (step 8)

- **No bug in the PR.**
- **Existing code** (`issues/raft-storage-hardstate-term-below-log.md`, an undocumented
  precondition): raft needs `HardState.Term` to be at least the term of the last entry (and of
  the snapshot), and `Storage` does not say so.
  - A single voter restarted from a `MemoryStorage` with entries of terms 1, 2, 3 and
    `HardState{Term: 1}` wins term 2 and appends an entry of term 2 after the term-3 entry: log
    terms `[1 2 3 2]`.
  - This is `TestProbeRaft47InconsistentStorage` in `notes/pr-verify/raft-47/raft47_probe_test.go`.
    It fails on `509271dac` and passes with the PR, which panics with
    `appending out-of-order term: 2 < 3`.
- **The restore change**: `TestProbeRaft47SnapshotHigherTerm` (same file).
  - On the base, a follower at term 2 restores a snapshot of term 11 and stays at term 2.
  - With the PR, it refuses the snapshot and steps down to term 11.
  - Logs: `notes/pr-verify/raft-47/probe-{pr-59be9c1e4,base-509271dac}.log`.
- **Reviewer's points, all resolved**:
  - The PR does not guard every path to an out-of-order log. A follower accepts a `MsgApp`
    whose entries' terms are above the message's term, because `handleAppendEntries` does not
    check them. The PR then panics only at that node's next won election, not at receipt.
  - No correct leader sends such a message, and the model's `isMessage` excludes it. The point is
    about the scope of a defense-in-depth check, not a bug.
  - Test: `notes/pr-verify/raft-47/review47_msgapp_test.go`, logs `review-*.log`.
  - The reviewer also corrected the issue's wording; it is fixed.
- **The upstream reviewers' comment** (lavacat, +1 by ahrtr) suggests the `appendEntry` check would
  be better in `newRaft`. The proof supports this as far as it goes: once the start state is
  consistent, raft keeps the property as long as its messages are well formed. A start-up check
  alone would not catch the malformed `MsgApp` above, though.
- **When a node steps down in `restore`**, `handleSnapshot` then answers at the new, higher term,
  which makes the sender step down. This is harmless, and no correct leader triggers it.

## Draft review comment (for the user to edit and post)

> I looked at when the two new checks can fire.
>
> - In `appendEntry`, `r.Term < lastTerm` requires a log whose last term is above the node's
>   term. raft never creates one from a consistent start: every entry it appends or accepts from a
>   correct leader is at most the current term, and a correct leader's snapshot is at most its
>   own term, which the follower has already adopted when `handleSnapshot` runs.
> - So in practice the check catches two things:
>   - a `Storage` whose `HardState.Term` is below the term of its last entry. This is reachable
>     through `RawNode`: a single voter with entries of terms 1, 2, 3 and `HardState{Term: 1}`
>     becomes leader at term 2 and appends `{Index: 4, Term: 2}` today;
>   - malformed messages: a `MsgSnap` whose snapshot term is above `m.Term` (refused by the new
>     `restore` check), or a `MsgApp` whose entries' terms are above `m.Term`. The latter is still
>     accepted by `handleAppendEntries`, and the new panic only fires at that node's next election
>     win.
>
> That supports @lavacat's suggestion: checking `HardState.Term >= lastTerm` (and the snapshot
> term) in `newRaft` would report the storage case at start-up, where it originates. It might also
> be worth stating that requirement in the `Storage.InitialState` docs. The `appendEntry` panic
> would then remain as defense-in-depth for malformed messages.
