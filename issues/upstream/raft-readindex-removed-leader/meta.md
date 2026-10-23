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
- **Branch**: `fix/raft-readindex-removed-leader` in `~/etcd-fixes/raft-readindex-removed-leader`, two commits
  (revised 2026-10-19 after review, below): 1917bb4 adds the test, which fails there; 3009105 is the fix. The
  first version (a15b631 test, 9fa83d5 fix, 30d3548 changelog; base 638f42739), pushed 2026-10-18 and opened as the
  PR, is kept locally as `backup/raft-readindex-removed-leader-v1`. The revision replaces it on
  `upamanyus/etcd-raft` by a force-push (`--force-with-lease=fix/raft-readindex-removed-leader:30d3548`, done
  2026-10-19 with the user's approval, as the reviewer asked for a rebase); the PR's head is now 3009105.
- **Base**: upstream `main` 1d3216d845a72ef5a78c55772ea220a931e2c3ef (2026-10-19, the merge of #535)
- **State**: merged (filed 2026-10-19; the revision, 3009105, merged by ahrtr the same day as 1931ff5be). The
  bot's `/cherry-pick` to release-3.7 (conflict in `raft.go`) and release-3.6 (`raft_test.go`) failed; ahrtr
  asked for manual cherry-picks to release-3.7, release-3.6 and etcd's release-3.5 (`raft/`), and reopened #534
  "to track the backport effort". The manual backports: etcd-io/raft#542 (release-3.7) and #541 (release-3.6),
  merged 2026-10-23; etcd-io/etcd#22652 (release-3.5), open. Before the merge, the PR description and the issue's
  test link were still to be edited on GitHub by the user.
- **Changelogs** (asked by ahrtr, #534 issuecomment-6374581035, 2026-10-23): each repository keeps its changelogs on
  `main` only (raft's release-3.6 has no `CHANGELOG/`), so two PRs, not one per backport. Not pushed or opened:
  - raft: `changelog/raft-readindex-removed-leader` in `~/etcd-fixes/raft-readindex-removed-leader-changelog`, off
    upstream `main` c51f010: e711b62 replaces #535's `pull/TODO` link in `CHANGELOG-3.8.md`; ac400cb adds new
    v3.7.1 and v3.6.1 sections linking the backport PRs (#542, #541), as raft's 3.7 changelog links its release-3.7
    PR #442. No 3.8 entry for #536 (r4314301990: a backported fix gets none there). Body: `changelog-pr-raft.md`.
  - etcd: `changelog/raft-readindex-removed-leader-3.5` in `~/etcd-fixes/raft-readindex-removed-leader-changelog-3.5`,
    off upstream `main` f3221acd1: 4689641f2, under v3.5.36 (TBC) in a `### Package \`raft\`` section (3.4's
    heading; 3.5 has no raft entry yet), linking #22652 (as 3.5 links its release-3.5 PRs). Body:
    `changelog-pr-etcd.md`.
- **Upstream issue**: [etcd-io/raft#534](https://github.com/etcd-io/raft/issues/534), filed 2026-10-19. Its test
  link (`blob/fix/raft-readindex-removed-leader/raft_test.go#L2227-L2260`) is off by 36 lines after the rebase;
  `issue.md` now has the permalink `blob/1917bb4/raft_test.go#L2263-L2296` and base 1d3216d84, to edit into the issue.
- **PR**: [etcd-io/raft#536](https://github.com/etcd-io/raft/pull/536), opened 2026-10-19 from this branch at
  30d3548; its body is `pr.md` (rewritten for the revision: the new base's permalinks, `IsVoter`, no conflict note).

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections.

## Duplicates checked (2026-10-16)

The sibling's searches (`IsSingleton`, `ReadIndex single member stale`, `"stale read" linearizable`): no duplicate,
no open PR. Related: etcd-io/raft#83 (open: make `StepDownOnRemoval` the default, which would avoid this case).

## Review (2026-10-19, ahrtr)

- [r4314290259](https://github.com/etcd-io/raft/pull/536#discussion_r4314290259): do not change `IsSingleton`'s
  API; add `ProgressTracker.IsVoter(id)` (code given) and check `r.trk.IsVoter(r.id) && r.trk.IsSingleton()` in
  `sendMsgReadIndexResponse`, with the comment given. Applied word for word.
- [r4314301990](https://github.com/etcd-io/raft/pull/536#discussion_r4314301990): no changelog entry, since the fix
  will be backported to stable releases (etcd-io/raft#534, issuecomment-6267699550). The changelog commit is dropped.
- [Comment 6268211200](https://github.com/etcd-io/raft/pull/536#issuecomment-6268211200): rebase (on #535, merged
  as 1d3216d; it moved the shortcut from `stepLeader` into `sendMsgReadIndexResponse`). Done: the test commit
  cherry-picked cleanly; the fix rewritten on the moved shortcut.

## The sibling PR

etcd-io/raft#535 (`fix/raft-readindex-singleton-stale`) merged 2026-10-19 (1d3216d); this branch is now on top of
it, so the conflict note is gone from `pr.md`. #535's changelog entry on `main` still links `pull/TODO`.

## Verification (go1.26.9 linux/amd64, 2026-10-19, base 1d3216d)

`TestReadOnlyForRemovedLeader` (the issue's example, after `TestReadOnlyDuplicateRequest`): `newNetwork(nil, nil)`,
peer 2 elected; peer 2 proposes `remove 2`, which commits at both; both apply it right after that `nt.send`; peer 1
`becomeCandidate`, `becomeLeader` and commits `y` (index 4); every read state of a read sent to peer 2 through
`nt.send` must have an index of at least 4. With the fix peer 2 produces none (its heartbeat at term 1 is ignored by
peer 1 at term 2, CheckQuorum and PreVote being off), so the check is vacuous there; kept so on purpose (the user's
decision, 2026-10-18): the test rules out a stale answer, not the absence of one.

- At the test commit 1917bb4 (`go test .`): only `TestReadOnlyForRemovedLeader` fails, at `raft_test.go:2293`,
  `"2" is not greater than or equal to "4"` (`read index`).
- At the fix commit 3009105: passes; `go test ./...` (raft, confchange, quorum, raftpb, rafttest, tracker) ok;
  `gofmt -l` empty; `go vet ./...` clean.

Not run: etcd's tests, `make verify`. Not reproduced on an etcd cluster.

## If a reviewer asks

- `IsVoter(id) && IsSingleton()`: one voter, and that voter is the leader; the API of `IsSingleton` is unchanged.
  The first version instead changed it to `IsSingleton(id)` (`Voters.VoteResult({id: true}) == quorum.VoteWon`),
  which also took the shortcut in a joint configuration whose halves are both `{leader}`; the reviewer's form does
  not, so that case still waits for heartbeat responses only a learner could send, as on `main`
  (`issues/raft-joint-self-quorum-read.md`, a separate finding).
- With this fix, a removed leader still answers a read once the remaining voter acknowledges its heartbeat in its
  term: a valid confirmation (no other leader can have been elected). Refusing reads at a removed leader outright is
  `StepDownOnRemoval` (etcd-io/raft#83).
- `ReadOnlyLeaseBased` at a removed leader still answers at once, as lease-based reads do anywhere: they are not
  confirmed with a quorum by design, and raft requires CheckQuorum with them, under which the removed leader steps
  down once the remaining voter stops answering. Not changed.
- Backports: the reviewer plans them (r4314301990). v3.7.0 has the same shortcut in `stepLeader` (before #535
  moved it); a cherry-pick to `release-3.7` needs #535 first or the check applied there. Not tried.
