# raft-readindex-singleton-stale

## Security classification (decide before filing)

A stale linearizable read in etcd, reachable only with a membership change (the member API: root when auth is on)
plus a network fault and a timing window; not by a client with ordinary access alone. Stale-read bugs have been
public issues upstream before (etcd-io/etcd#741, #3879, #14140, #16666, #20418; etcd-io/raft#392). So: candidate
written; the user decides whether to file it publicly or through etcd's security process first.

Evidence, at etcd-io/etcd `main` b25719d10 (raft `v3.7.0`, which has the same shortcut at `raft.go:1355-1361`):

- etcd's `raftConfig` (`server/etcdserver/bootstrap.go`) sets neither `ReadOnlyOption` (so `ReadOnlySafe`, the zero
  value) nor `StepDownOnRemoval` (false); linearizable reads go through `raft.ReadIndex`
  (`server/etcdserver/read/read.go`, `requestCurrentIndex`), take the `ReadState`'s index, wait for apply to reach it
  and serve. Nothing in etcd checks that the leader committed in its term; etcd's own `FirstCommitInTermNotify` resend
  assumes raft postpones those reads.
- Scenario 1 (the issue's example) in etcd: a two-member cluster, leader 2; `member remove 2` (strict reconfig check
  passes while both are connected). Member 2 keeps applying for up to 1 s after it applies its own removal
  (`applyAll` → `stopWithDelay(1s)`), so it can commit, apply and acknowledge a write `x` at the next index. If the
  messages carrying that commit index to member 1 are lost (a partition at that moment), member 1, alone in `{1}`,
  wins the next election after 2 stops; a linearizable read reaching its raft between `becomeLeader` and its next
  `Ready` (one WAL write) is answered at the old commit index, and the read misses the acknowledged `x`.
- Scenario 2 (removed leader): needs member 1 to be elected and commit within member 2's 1 s stop delay, and
  CheckQuorum (on in etcd) also deposes member 2 after an election timeout; so in etcd its staleness window is
  about one second. Less likely than scenario 1.
- Not reproduced on etcd; reasoning from code only.

## Candidate

- **Finding**: `issues/raft-readindex-singleton-stale.md` (the new-leader case; the removed-leader case is the
  sibling candidate `issues/upstream/raft-readindex-removed-leader/`, split off 2026-10-18)
- **Target**: etcd-io/raft, `main` (also in v3.7.0, which etcd `main` uses)
- **Branch**: `fix/raft-readindex-singleton-stale` in `~/etcd-fixes/raft-readindex-singleton-stale`, two commits:
  170b51a adds the test, which fails there; 3552656 is the fix. The fork's branch has the earlier combined fix
  (77ab0c9) until this is force-pushed (`https://github.com/upamanyus/etcd-raft/tree/fix/raft-readindex-singleton-stale`,
  the branch the links in `issue.md` name; its lines 2154-2188 are the test).
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft, revised after the user's review and a code review, split in two (2026-10-18)
- **Upstream issue**: — (the issues do not mention each other; only the PRs do, in their conflict note)
- **PR**: — (then replace `pull/TODO` in the fix commit's `CHANGELOG/CHANGELOG-3.8.md` entry with its number, and
  `#<other PR>` in `pr.md`)

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections.

## Duplicates checked (2026-10-16)

Searches on `repo:etcd-io/raft repo:etcd-io/etcd`: `IsSingleton` (0 results), `ReadIndex single member stale`,
`"stale read" linearizable`. No duplicate, no open PR. Related, closed: etcd-io/raft#392 (ReadIndex retries with a
reused request context), #397 and #398 (the user's earlier work on that); etcd-io/raft#83 (open: make
`StepDownOnRemoval` the default; would avoid the removed-leader case only).

## The sibling PR

This PR and `fix/raft-readindex-removed-leader` are independent, each off `main`, and conflict: in `raft.go` (this
one removes the shortcut from `stepLeader`, the other changes its call to `IsSingleton(r.id)`) and in
`CHANGELOG-3.8.md` (both add a Bug Fixes entry); their tests merge cleanly. After both, this PR's moved shortcut
must call `IsSingleton(r.id)` (the other changes the signature), or it does not compile. Merged that way, `raft.go`
and `tracker/tracker.go` are those of the combined fix (77ab0c9), checked 2026-10-18. Both PRs say so and offer
one combined PR instead.

## Verification (go1.26.9 linux/amd64)

`TestReadOnlyForNewSingleVoterLeader` (the issue's example, after `TestReadOnlyForNewLeader`): `newNetwork(nil,
nil)`, peer 2 elected; peer 2 proposes `remove 2` (index 2) and `x` (index 3) in one `nt.send` (a leader that
applied its own removal drops proposals), with a `msgHook` dropping messages to peer 1 whose commit is at least 3;
peer 1 has commit 2, peer 2 commit 3; both apply the removal right after that `nt.send`; peer 1 `becomeCandidate`,
`becomeLeader`; a read sent to peer 1 through `nt.send` must have a read state with an index of at least 3 (only
the guarantee: not when, nor at which index, it is answered).

- At the test commit 170b51a (`go test . -run TestReadOnlyForNewSingleVoterLeader`): fails, `"2" is not greater
  than or equal to "3"` (`read index`).
- At the fix commit 3552656: passes; `go test ./...` (raft, confchange, quorum, raftpb, rafttest, tracker) ok;
  `gofmt -l` empty; `go vet ./...` clean.

Not run: etcd's tests, `make verify`. Not reproduced on an etcd cluster.

## If a reviewer asks

- Why move the shortcut into `sendMsgReadIndexResponse` rather than below the `committedEntryInCurrentTerm()`
  check in `stepLeader`: postponed requests are released through `sendMsgReadIndexResponse`
  (`releasePendingReadIndexMessages`), not `stepLeader`; there, a released request at a single voter would take the
  `ReadOnlySafe` heartbeat round, which no other voter answers. The reorder-only variant was run (2026-10-18): the
  test fails, the read is never answered.
- Why the read's answer now waits: the no-op of the new term commits only once the leader has persisted it (its
  own `MsgAppResp`); before that, its commit index can miss entries the previous leader committed.
- A more general fix: in the `ReadOnlySafe` path, answer as soon as the leader's own acknowledgement wins the
  quorum (after `recvAck(r.id, ...)`), instead of only in the `MsgHeartbeatResp` handler. It would make the shortcut
  unnecessary; it is a larger change to the read-only state machine, not needed for this bug.
- `ReadOnlyLeaseBased` at a single voter now also waits for the first commit of the leader's term (it used to take
  the shortcut too). Before that commit, its multi-voter path postpones as well.
- Related, not changed: `switchToConfig`'s `maybeCommit` does not release postponed reads, only the `MsgAppResp`
  path does. Not reachable under `doc.go`'s protocol (a node does not campaign with committed conf changes
  unapplied, and a leader's first commit in its term goes through `MsgAppResp`); only with `Advance` before
  `ApplyConfChange` (`issues/raft-switchtoconfig-pending-reads.md`).
- The verified fork (mit-pdos etcd-grove) carries the combined change on v3.7.0 (`509271dac`), verified at
  `raft.Step`.
- Backports: v3.7.0 (`raft.go:1355-1361`) has the same shortcut; not tried on a release branch.
