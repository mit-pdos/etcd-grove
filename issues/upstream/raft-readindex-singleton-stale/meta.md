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
- **Branch**: `fix/raft-readindex-singleton-stale` in `~/etcd-fixes/raft-readindex-singleton-stale`, two commits:
  3130f9e adds the tests, which fail there; 77ab0c9 is the fix. Not yet pushed: `upamanyus/etcd-raft` has an
  earlier single-commit version (dcb4fe2) until the force-push
  (`https://github.com/upamanyus/etcd-raft/tree/fix/raft-readindex-singleton-stale`, the branch the links in
  `issue.md` name).
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft, revised after the user's review and a code review (2026-10-18)
- **Upstream issue**: —
- **PR**: — (then replace `pull/TODO` in the fix commit's `CHANGELOG/CHANGELOG-3.8.md` entry with its number)

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections.

## Duplicates checked (2026-10-16)

Searches on `repo:etcd-io/raft repo:etcd-io/etcd`: `IsSingleton` (0 results), `ReadIndex single member stale`,
`"stale read" linearizable`. No duplicate, no open PR. Related, closed: etcd-io/raft#392 (ReadIndex retries with a
reused request context), #397 and #398 (the user's earlier work on that); etcd-io/raft#83 (open: make
`StepDownOnRemoval` the default; would avoid the removed-leader case only).

## Verification (go1.26.9 linux/amd64)

Both tests use `newNetwork(nil, nil)` with peer 2 elected, deliver every message through `nt.send`, and apply the
removal at each peer right after the `nt.send` in which the peer learns it is committed (a leader that applied its
own removal drops proposals, so `x` is proposed in the same `nt.send` as the removal). Each asserts only the
guarantee: a read state for the read must have an index at least that of the last entry committed before it.

- `TestReadOnlyForNewSingleVoterLeader` (the issue's example): peer 2 proposes `remove 2` (index 2) and `x` (index
  3) in one `nt.send`, with a `msgHook` dropping messages to peer 1 whose commit is at least 3; peer 1 has commit 2,
  peer 2 commit 3; both apply the removal; peer 1 `becomeCandidate`, `becomeLeader`; a read at peer 1 must have an
  index of at least 3.
- `TestReadOnlyForRemovedLeader`: peer 2 proposes `remove 2`, which commits at both; both apply it; peer 1
  `becomeCandidate`, `becomeLeader` and commits `y` (index 4); every read state of a read sent to peer 2 must have
  an index of at least 4. With the fix peer 2 produces none (its heartbeat at term 1 is ignored by peer 1 at term 2,
  CheckQuorum and PreVote being off), so the check is vacuous there; kept so on purpose (the user's decision,
  2026-10-18): the test rules out a stale answer, not the absence of one.

- At the tests commit 3130f9e (`go test . -run 'TestReadOnlyForNewSingleVoterLeader|TestReadOnlyForRemovedLeader'`):
  both fail, `"2" is not greater than or equal to "3"` and `"2" is not greater than or equal to "4"` (`read index`).
- At the fix commit 77ab0c9: both pass; `go test ./...` (raft, confchange, quorum, raftpb, rafttest, tracker) ok;
  `gofmt -l` empty; `go vet ./...` clean.
- A temporary test (not on the branch): a leader of `{1}` that enters the joint configuration `{1}&&{1}` (adding
  a learner with an explicit transition) gets no answer to a read on `main` (it waits for heartbeat responses that
  only the learner could send) and an immediate one with the fix.

Not run: etcd's tests, `make verify`. Not reproduced on an etcd cluster.

## If a reviewer asks

- `IsSingleton()` becomes `IsSingleton(id)`, "id on its own constitutes a quorum", implemented as `Voters.VoteResult({id: true})
  == quorum.VoteWon`: the old one only counted voters, so a leader that removed itself saw one voter that is not
  itself; the quorum form also covers a joint configuration whose halves are both `{leader}` (see above). An empty
  configuration counts as won, but raft refuses to remove the last voter.
- The signature change breaks callers of the exported `ProgressTracker.IsSingleton()` outside raft; there are none
  in raft or in etcd (`main` b25719d10, `server/`, `client/`). Deliberate: a caller must now say which node it means,
  which is the ambiguity behind this bug. Alternative if the API must stay: keep `IsSingleton()` (deprecated) and add
  the id form under another name.
- Why move the shortcut rather than add `committedEntryInCurrentTerm()` to it: postponed requests are released
  through `sendMsgReadIndexResponse`; without the shortcut there, a postponed request at a single voter would go
  through the heartbeat round, which nobody answers, and never be released.
- A more general fix: in the `ReadOnlySafe` path, answer as soon as the leader's own acknowledgement wins the
  quorum (after `recvAck(r.id, ...)`), instead of only in the `MsgHeartbeatResp` handler. It would make the shortcut
  unnecessary; it is a larger change to the read-only state machine, not needed for this bug.
- `ReadOnlyLeaseBased` at a removed leader still answers at once, as lease-based reads do anywhere: they are not
  confirmed with a quorum by design, and raft requires CheckQuorum with them, under which the removed leader steps
  down once the remaining voter stops answering. Not changed.
- `ReadOnlyLeaseBased` at a single voter now also waits for the first commit of the leader's term (it used to take
  the shortcut too). Before that commit, its multi-voter path postpones as well.
- Related, not changed: reads postponed until the leader's first commit in its term are not released when that
  commit happens through a configuration change (`switchToConfig`'s `maybeCommit`), only through `MsgAppResp`
  (`issues/raft-switchtoconfig-pending-reads.md`).
- The verified fork (mit-pdos etcd-grove) carries the same change on v3.7.0 (`509271dac`), verified at `raft.Step`.
- Backports: v3.7.0 (`raft.go:1355-1361`) has the same shortcut; not tried on a release branch.
