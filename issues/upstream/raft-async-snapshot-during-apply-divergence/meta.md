# raft-async-snapshot-during-apply-divergence

## Security

Not a security report. It needs `AsyncStorageWrites`, which etcd does not enable (no use in etcd's sources), and a
follower behind the leader's compacted log while it applies older entries; a client of an application built on
raft cannot cause it by itself.

## Candidate

- **Finding**: `issues/raft-async-snapshot-during-apply-divergence.md`
- **Target**: etcd-io/raft, `main` (the same `restore`/`RawNode` code in v3.7.0)
- **Branch**: `fix/raft-async-snapshot-during-apply-divergence` in `~/etcd-fixes/raft-async-snapshot-during-apply-divergence`,
  two commits: 831199f adds `TestRawNodeAsyncSnapshotDuringApply` (`rawnode_test.go`, lines 967-1044, after
  `TestRawNodeConsumeReady`), which fails there; b60b90c is the fix (`rawnode.go` only, 35 lines added, 17 removed:
  `storageAppendHeld` and its uses in `readyWithoutAccept`, `acceptReady`, `HasReady`). No changelog commit (a bug
  fix the maintainers would backport).
- **Base**: upstream `main` 1931ff5beacc1e2539003c0c70f096285f04c425 (2026-10-19; still `main` on 2026-10-23)
- **State**: draft (2026-10-23). Not pushed.
- **Upstream issue**: —
- **PR**: —

Split off `raft-snapshot-during-apply-stale-confchange` on 2026-10-23 (the skill's split rule: a distinct trigger,
`AsyncStorageWrites` with no conf change, a distinct symptom, the state machine, and a distinct workaround). Until
then its fix was only part of that candidate's branch.

Push: `git -C ~/etcd-fixes/raft-async-snapshot-during-apply-divergence push origin fix/raft-async-snapshot-during-apply-divergence`;
then check the issue's link `#L967-L1044` on GitHub.

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version".

Commit messages (drafts for the user to rewrite):

- `raft: test snapshot received while applying entries with async writes` (no body)
- `raft: apply a snapshot after earlier entries with async writes` — "With asynchronous storage writes, a snapshot
  could be applied before older committed entries, which were then applied on top of it."

## Duplicates checked

2026-10-21: `repo:etcd-io/raft` `AsyncStorageWrites snapshot` (#8, #110), `MsgStorageAppend snapshot` (#8, #161),
`async storage writes snapshot` (#8, #37), `LocalApplyThread` (#8); the review threads of #8 and of
etcd-io/etcd#14627 (where #8 started): none about a snapshot handed out while committed entries are being applied.
2026-10-23: `AsyncStorageWrites snapshot` (#8, #110), `MsgStorageApply snapshot` (#161, #8), `async apply snapshot
order` (#474 open, a scenario-test DSL, unrelated; #8), `LocalApplyThread` (#8); every etcd-io/raft issue and PR
created or updated since 2026-10-18 (version bumps and the read-index fixes #533-#536); the 30 most recently updated
open PRs: none touches this. No duplicate, no open PR.

## Other candidates

- **`raft-snapshot-during-apply-stale-confchange`** (draft, fix 9dc2d50): its fix contains this branch's
  `rawnode.go` change byte for byte (the same hunks, the same doc comment), because with `AsyncStorageWrites` it
  needs the snapshot applied after the older entries' `ApplyConfChange` calls. `git merge-tree --write-tree b60b90c
  9dc2d50` is clean in either order (identical hunks); the merged tree vets and passes `go test ./...`, both tests
  included. This fix alone does not fix that one (its test still fails, three of four subtests, with this fix on
  `main`); that fix alone fixes this one (this test passes on it). Each PR ends with a note on the overlap (the
  skill's split note, adapted: they do not conflict).
- Merges cleanly with `fix/raft-advance-before-applyconfchange` (fd30b41), `raft-memorystorage-initialstate-unlocked`
  (15190e3) and `raft-readindex-singleton-stale` (3d0bd8a) (`git merge-tree`, 2026-10-23).

## Why the fix works

At the base, in the test: node 2 steps `MsgApp` committing "a" at index 1; once it is stable, `Ready` hands it to
the apply thread (`applying` 1, `applied` 0). The `MsgSnap` at index 2 is above the commit index, so `restore`
restores it into the unstable log. `hasNextCommittedEnts` holds back new committed entries while a snapshot is
pending, but nothing holds the snapshot back for the entries already handed out: the next `Ready` puts it in a
`MsgStorageAppend`. The append thread runs first: state "ab"; its response (`appliedSnap`) moves `applied` to 2. The
apply thread then applies index 1: "aba".

With the fix, `storageAppendHeld` is true while an unstable snapshot is not yet handed out and `applying >
applied`. Meanwhile `Ready` hands nothing to the append thread: not the snapshot, not the entries after it, not a
`HardState` (its commit index is the snapshot's), not `msgsAfterAppend` (the `MsgAppResp` acknowledging the
snapshot must wait until it is durable); `acceptReady` keeps `msgsAfterAppend` and does not mark the unstable log
in progress; `HasReady` ignores them. The apply thread applies "a" and its response makes `applied == applying`;
the next `Ready` hands the snapshot out, and the append thread makes the state "ab".

- The condition can only become true at a restore: no committed entries are handed out while a snapshot is pending
  (`hasNextOrInProgressSnapshot`), so it never holds back entries the apply thread is waiting for.
- Without `AsyncStorageWrites` it never holds (`rn.asyncStorageWrites` is the first conjunct): the snapshot's
  `Ready` comes after the `Advance` of the previous one.
- The hold always ends: the apply thread must deliver its response (the documented contract), and nothing the
  apply thread needs is held.

## Why the test shows the bug, not a misuse

`Config.AsyncStorageWrites`: `MsgStorageAppend` carries "snapshots to apply", the writes being to "local storage
(raft log and state machine)"; "Messages to different targets can be processed in any order"; each thread processes
its own messages in order and delivers their responses after the write. The test does exactly that, with the
append thread running ahead of the apply thread (one order the documentation allows). doc.go's example append thread
only saves the snapshot to storage (`saveToStorage`); an application following it literally never installs the
snapshot's state, a different gap, asked about in the issue ("Is that required?"). The leader's messages are built
by hand (a `MsgApp` committing index 1, a `MsgSnap` at index 2), each of a kind a leader sends to a follower behind
its compaction point; the test drives a `RawNode` like the other async tests and the sibling candidate's.

## Verification (go1.26.9 linux/amd64, 2026-10-23)

- At the tests commit 831199f (`go test -count=1 -run 'TestRawNodeAsyncSnapshotDuringApply$' .`): fails,
  `expected: "ab"`, `actual  : "aba"` (`rawnode_test.go:1043`).
- At the fix b60b90c (same tree as the first fix commit 48b5740, only the subject shortened): passes; `go test
  -count=1 ./...` (raft, confchange, quorum, raftpb, rafttest, tracker) ok, also with `-race`; `gofmt -l .` empty;
  `go vet ./...` clean. The interaction tests' async traces (`testdata/async_storage_writes*.txt`) are unchanged.
- Merged with the sibling's 9dc2d50 (`git merge-tree`, archived tree): `go vet` clean, `go test ./...` ok, both
  `TestRawNodeAsyncSnapshotDuringApply` and `TestRawNodeSnapshotDuringConfChangeApply` pass.
- Earlier (2026-10-21, on the sibling's branch, temporary tests not on any branch): a `MsgApp` at index 3, a
  heartbeat and a probe at index 2 arriving during the hold are answered with no rejection (only the heartbeat
  response goes out; the `MsgAppResp`s are held and go out after the release).
- Not run: `make verify`, golangci-lint. Not reproduced in a cluster.

## If a reviewer asks

Candidate layers and fixes:

- **(1) Hold the snapshot in `RawNode` (taken).** The bug is raft handing out work in an order the documented thread
  model cannot keep; `log.go` already holds committed entries back while a snapshot is pending ("Doing so raises
  questions about what should be applied first"), and this is the other direction of the same rule. It changes
  nothing without `AsyncStorageWrites` and nothing with it unless a snapshot arrives while entries are being applied.
- **(1') Refuse the snapshot in `raft.restore` while `applying > applied`**: the follower answers as for an ignored
  snapshot, which leaves the leader's progress in `StateSnapshot` until `ReportSnapshot`; a second transfer each time
  (measured for the sibling's first fix). The hold restores at once, so the leader does not send it again.
- **(2) Document the order** (the append thread waits for the apply thread before a snapshot) and fix doc.go's
  example: keeps every application's burden and contradicts "processed in any order"; raft has the information to
  order it itself.
- **(3) Send the snapshot to the apply thread too, ordered with the entries**: an interface change for every
  `AsyncStorageWrites` user.

Other questions:

- Cost: only with `AsyncStorageWrites` and only while a snapshot waits for older entries: the follower persists
  nothing meanwhile, so its `MsgAppResp`s and vote responses wait for the apply thread's response; heartbeat
  responses do not wait.
- Why the `HardState` and the later entries wait too: the `HardState` after the restore commits the snapshot's
  index, which must not be persisted before the snapshot; entries after the snapshot cannot be appended before it.
- Backports: v3.7.0 has the same code; not tried on `release-3.7`.

## check.py (2026-10-23)

No FAIL. WARNs, decided:

- The comment added: `storageAppendHeld`'s doc comment says why nothing goes to the append thread and why it never
  holds without `AsyncStorageWrites`, which the code does not show; kept.
- The issue's 397 words (aim 380, rewritten free-form with the cause after the 2026-10-23 review): kept; the
  configuration (what the append thread does) is needed to show it is not a misuse, and the cause has two halves
  (raft holds entries back for a snapshot but not a snapshot for entries; the threads may run in any order).
- The PR's 148 words (aim 90): kept; the approved raft example has 136, and the cause has two halves (raft hands the
  snapshot out; the threads may run in any order) plus the overlap note.
