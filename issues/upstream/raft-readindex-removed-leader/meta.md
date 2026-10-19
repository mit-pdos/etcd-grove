# raft-readindex-removed-leader

## Security

The removed-leader scenario of `raft-readindex-singleton-stale` (its `meta.md`, "Security classification",
scenario 2): a stale linearizable read in etcd only with a membership change plus a network fault, within member 2's
1 s stop delay and before CheckQuorum deposes it. Not reachable by a client with ordinary access alone; the user
decides how to file, as for the sibling.

## Candidate

- **Finding**: `issues/raft-readindex-removed-leader.md` (split off `issues/raft-readindex-singleton-stale.md`,
  2026-10-18)
- **Target**: etcd-io/raft, `main` (also in v3.7.0, which etcd `main` uses)
- **Branch**: `fix/raft-readindex-removed-leader` in `~/etcd-fixes/raft-readindex-removed-leader`, three commits:
  a15b631 adds the test, which fails there; 9fa83d5 is the fix; 30d3548 adds the changelog entry. Pushed 2026-10-18
  to `upamanyus/etcd-raft` (`https://github.com/upamanyus/etcd-raft/tree/fix/raft-readindex-removed-leader`, the branch the links in
  `issue.md` name; its lines 2227-2260 are the test).
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: filed (the issue and the PR, 2026-10-19)
- **Upstream issue**: [etcd-io/raft#534](https://github.com/etcd-io/raft/issues/534), filed 2026-10-19 (the issues do not mention each other; only the PRs do, in their conflict note)
- **PR**: [etcd-io/raft#536](https://github.com/etcd-io/raft/pull/536), opened 2026-10-19 from this branch at 30d3548;
  its body is `pr.md`. Still to do: the changelog commit 30d3548's `CHANGELOG/CHANGELOG-3.8.md` entry links `pull/TODO`;
  a new commit on the branch (not a force-push) should make it `pull/536`

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections.

## Duplicates checked (2026-10-16)

The sibling's searches (`IsSingleton`, `ReadIndex single member stale`, `"stale read" linearizable`): no duplicate,
no open PR. Related: etcd-io/raft#83 (open: make `StepDownOnRemoval` the default, which would avoid this case).

## The sibling PR

This PR and `fix/raft-readindex-singleton-stale` are independent, each off `main`, and conflict: in `raft.go` (the
other removes the shortcut from `stepLeader` and moves it into `sendMsgReadIndexResponse`; this one changes its call
to `IsSingleton(r.id)`) and in `CHANGELOG-3.8.md` (both add a Bug Fixes entry); their tests merge cleanly. After
both, the other's moved shortcut must call `IsSingleton(r.id)`, or it does not compile. Both PRs say so and offer
one combined PR instead.

## Verification (go1.26.9 linux/amd64)

`TestReadOnlyForRemovedLeader` (the issue's example, after `TestReadOnlyDuplicateRequest`, so that it does not
conflict with the sibling's test): `newNetwork(nil, nil)`, peer 2 elected; peer 2 proposes `remove 2`, which
commits at both; both apply it right after that `nt.send`; peer 1 `becomeCandidate`, `becomeLeader` and commits `y`
(index 4); every read state of a read sent to peer 2 through `nt.send` must have an index of at least 4. With the
fix peer 2 produces none (its heartbeat at term 1 is ignored by peer 1 at term 2, CheckQuorum and PreVote being
off), so the check is vacuous there; kept so on purpose (the user's decision, 2026-10-18): the test rules out a
stale answer, not the absence of one.

- At the test commit a15b631 (`go test . -run TestReadOnlyForRemovedLeader`): fails, `"2" is not greater than or
  equal to "4"` (`read index`).
- At the fix commit 9fa83d5: passes; `go test ./...` (raft, confchange, quorum, raftpb, rafttest, tracker) ok;
  `gofmt -l` empty; `go vet ./...` clean.
- A temporary test (2026-10-18, with the combined fix; this fix makes the same check at the shortcut): a leader of
  `{1}` that enters the joint configuration `{1}&&{1}` (adding a learner with an explicit transition) gets no answer
  to a read on `main` (it waits for heartbeat responses only the learner could send) and an immediate one with
  `IsSingleton(r.id)` (`issues/raft-joint-self-quorum-read.md`).

Not run: etcd's tests, `make verify`. Not reproduced on an etcd cluster.

## If a reviewer asks

- `IsSingleton()` becomes `IsSingleton(id)`, "id on its own constitutes a quorum of the current configuration",
  implemented as `Voters.VoteResult({id: true}) == quorum.VoteWon`: the old one only counted voters, so a leader
  that removed itself saw one voter that is not itself; the quorum form also covers a joint configuration whose
  halves are both `{leader}`. An empty configuration counts as won, but raft refuses to remove the last voter.
  `stepLeader`'s comment "only one voting member (the leader) in the cluster" is left as it is: it now holds.
- The signature change breaks callers of the exported `ProgressTracker.IsSingleton()` outside raft; there are none
  in raft or in etcd (`main` b25719d10, `server/`, `client/`). Deliberate: a caller must now say which node it means,
  which is the ambiguity behind this bug. Alternative if the API must stay: keep `IsSingleton()` (deprecated) and add
  the id form under another name.
- With this fix, a removed leader still answers a read once the remaining voter acknowledges its heartbeat in its
  term: a valid confirmation (no other leader can have been elected). Refusing reads at a removed leader outright is
  `StepDownOnRemoval` (etcd-io/raft#83).
- `ReadOnlyLeaseBased` at a removed leader still answers at once, as lease-based reads do anywhere: they are not
  confirmed with a quorum by design, and raft requires CheckQuorum with them, under which the removed leader steps
  down once the remaining voter stops answering. Not changed.
- Backports: v3.7.0 has the same `IsSingleton`; not tried on a release branch.
  The changelog entry is in `CHANGELOG-3.8.md` (v3.8.0, Bug Fixes): v3.7.0 was released 2026-06-21, `main` is
  the 3.8 line, and raft keeps its changelogs on `main` only (`release-3.6` removed its copy; `release-3.7`'s is a
  stale alpha one). etcd uses v3.7.0, so the fix reaches etcd only with v3.8.0 or a v3.7.1 patch release, which
  raft has never made (3.6 stopped at v3.6.0; `release-3.7` has only Go bumps since v3.7.0): the maintainers'
  call; if wanted, cherry-pick the fix commits to `release-3.7` in a separate PR and add a v3.7.1 section to
  `CHANGELOG-3.7.md` on `main`. (Checked 2026-10-18.)
