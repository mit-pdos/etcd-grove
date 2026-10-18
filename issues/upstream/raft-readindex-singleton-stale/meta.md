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

- **Finding**: `issues/raft-readindex-singleton-stale.md`
- **Target**: etcd-io/raft, `main` (also in v3.7.0, which etcd `main` uses)
- **Branch**: `fix/raft-readindex-singleton-stale` in `~/etcd-fixes/raft-readindex-singleton-stale` (commit 69341e121, message rewritten and force-pushed 2026-10-18; was 32de820fe), pushed 2026-10-18 to `upamanyus/etcd-raft`
  (`https://github.com/upamanyus/etcd-raft/tree/fix/raft-readindex-singleton-stale`), the branch the links in `issue.md` name.
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft
- **Upstream issue**: —
- **PR**: —

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections.

## Duplicates checked (2026-10-16)

Searches on `repo:etcd-io/raft repo:etcd-io/etcd`: `IsSingleton` (0 results), `ReadIndex single member stale`,
`"stale read" linearizable`. No duplicate, no open PR. Related, closed: etcd-io/raft#392 (ReadIndex retries with a
reused request context), #397 and #398 (the user's earlier work on that); etcd-io/raft#83 (open: make
`StepDownOnRemoval` the default; would avoid the removed-leader case only).

## Verification (go1.26.9 linux/amd64)

`TestReadOnlyForNewSingleVoterLeader` (in `raft_test.go`, after `TestReadOnlyForNewLeader`) is the issue's example:
`newNetwork(nil, nil)`; peer 2 campaigns, proposes `remove 2` (index 2), then `x` (index 3) with a `msgHook` dropping
messages to peer 1 whose commit is at least 3; asserts peer 2's commit is 3 and peer 1's is 2; peer 1
`applyConfChange`s the removal, `becomeCandidate`, `becomeLeader`; steps a local `MsgReadIndex`, then
`advanceMessagesAfterAppend` (its empty entry at index 4 commits); asserts `readStates == [{Index: 4}]`.

- At the base (fix absent, test added): `go test . -run 'TestReadOnlyForNewSingleVoterLeader$'` fails, actual
  `[{Index:0x2 ...}]`.
- With the fix: the test passes; `go test . ./rafttest/` ok; `gofmt -l raft.go raft_test.go` empty;
  `go vet . ./rafttest/` clean.
- The removed-leader case, not on the branch (temporary test, kept at
  `.claude-D/jobs/685db998/tmp/raft-readindex-singleton-stale/removed_leader_tmp_test.go`): peers 1 and 2 apply
  `remove 2` (commit 2), peer 2 is isolated, peer 1 wins term 2 and commits `y` (commit 4); a read at peer 2 (still
  leader of term 1) gives `[{Index:2}]` at the base, no read state with the fix.

Not run: `confchange`, `quorum`, `tracker` and the other packages (the change is in package `raft` only), etcd's
tests, `make verify`. Not reproduced on an etcd cluster.

## If a reviewer asks

- Why move the shortcut rather than add `committedEntryInCurrentTerm()` to it: postponed requests are released
  through `sendMsgReadIndexResponse`; without the shortcut there, a postponed request at a single voter would go
  through the heartbeat round, which nobody answers, and never be released.
- Why the voter check: a leader that removed itself (`StepDownOnRemoval` false) sees `IsSingleton` for a
  configuration it is not in; without the check it answers from a commit index that is no longer current after it
  is deposed. With the check it goes through the heartbeat round, which needs the actual voter's acknowledgement.
  Alternative: change `IsSingleton` to take the leader's id; it has no other caller, but it is exported on
  `ProgressTracker`.
- `ReadOnlyLeaseBased` at a single voter now also waits for the first commit of the leader's term (it used to take
  the shortcut too). Before that commit, its multi-voter path postpones as well.
- The verified fork (mit-pdos etcd-grove) carries the same change on v3.7.0 (`509271dac`), verified at `raft.Step`.
- Backports: v3.7.0 (`raft.go:1355-1361`) has the same shortcut; not tried on a release branch.
