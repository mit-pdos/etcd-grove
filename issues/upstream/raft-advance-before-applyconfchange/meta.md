# raft-advance-before-applyconfchange

## Security

Not a security report. The trigger is the application's own ordering of `Advance` and `ApplyConfChange` and two
membership changes in a row; a client of an application built on raft cannot cause it by itself.

## Candidate

- **Findings**: `issues/raft-advance-before-applyconfchange.md`; related: `etcd-leader-advance-before-applyconfchange.md`
  (etcd's half, its own candidate) and, judged not issues (`issues/nonissues/`), `raft-track-confchange-application.md`
  (the guard fix, alternative (b) below); `raft-document-confchange-before-advance.md` was deleted on 2026-10-23 as a
  duplicate of this candidate.
- **Target**: etcd-io/raft, `main` (the same documentation and guards in v3.7.0, which etcd `main` uses)
- **Branch**: `fix/raft-advance-before-applyconfchange` in `~/etcd-fixes/raft-advance-before-applyconfchange`, one
  commit: fd30b41a2 (documentation only: `doc.go`, `README.md`, `node.go`, `raft.go`; 9 lines added, 5 removed).
- **Reproduction branch**: `repro/raft-advance-before-applyconfchange` in
  `~/etcd-fixes/raft-advance-before-applyconfchange-repro`, one commit, 3dcedb6af, adding
  `TestNodeAdvanceBeforeApplyConfChange` to `node_test.go` (lines 1063-1150). Not part of the PR (below). The issue
  links it there.
- **Base**: upstream `main` 1931ff5beacc1e2539003c0c70f096285f04c425 (2026-10-19; still `main` on 2026-10-23, so
  not rebuilt)
- **State**: draft (2026-10-23). Not pushed (neither branch is on the fork, `git ls-remote origin`, 2026-10-23).
- **Upstream issue**: —
- **PR**: —

Push (both branches; the issue links the second):
`git -C ~/etcd-fixes/raft-advance-before-applyconfchange push origin fix/raft-advance-before-applyconfchange` and
`git -C ~/etcd-fixes/raft-advance-before-applyconfchange-repro push origin repro/raft-advance-before-applyconfchange`;
then check the issue's link `#L1063-L1150` on GitHub.

Commit messages (drafts for the user to rewrite):

- `raft: document that conf changes must be applied before Advance` — "Raft's checks for a pending conf change
  trust the applied index, which Advance moves even if the conf change has not been applied yet."
- (reproduction branch) `raft: test Advance before ApplyConfChange` (no body)

No changelog entry: a documentation change.

## Why a documentation-only PR, and its shape

No test can fail before a doc change and pass after it, so the PR is the one documentation commit and the
reproduction is a test of the package on a branch of its own, which the issue links (the skill's documented shape
for a documentation fix, step 7; `check.py` checks it). Committing the test on the fix branch was considered and
rejected: as written it fails with the fix too, and rewritten to follow the documented order it would pass at the
base as well, testing nothing the PR changes.

## Duplicates checked (2026-10-21, with the token; again 2026-10-23)

2026-10-23 (unauthenticated): `repo:etcd-io/raft Advance ApplyConfChange` (#8), `pendingConfIndex` (#44, #354,
#381, #32), `hasUnappliedConfChanges` (#469, #456, #234, #32), `confchange updated:>=2026-10-18` (0),
`repo:etcd-io/etcd ApplyConfChange Advance updated:>=2026-10-18` (0); every etcd-io/raft issue and PR created or
updated since 2026-10-18 (version bumps, the read-index fixes #533-#536) and the 30 most recently updated open PRs:
no duplicate, no open PR. #381 (TLA+ spec) and #458 (TLA+, the campaign guard) touch the guards' model, not the
order of `Advance` and `ApplyConfChange`.


`repo:etcd-io/raft Advance ApplyConfChange` (issues: 0; PRs: #8, async storage writes, unrelated),
`repo:etcd-io/raft hasUnappliedConfChanges` (#456 open, TLA+ spec lacks the guard; #234 closed, async split brain
answered by the guard, which assumes the conf change is applied before the applied index moves; PRs #469 open, TLA+
only, #32 closed, scan pagination), `repo:etcd-io/raft pendingConfIndex applied` (#354 open, a rejected conf change
is a silent no-op; PR #44 open, error on ignored proposal), `repo:etcd-io/etcd Advance ApplyConfChange leader`
(#4203 closed, below; others unrelated), `repo:etcd-io/raft Advance applying conf` (0). No duplicate, no open PR.

etcd-io/etcd#4203 (2016) asked exactly whether a `Ready`'s conf change must be applied before `Advance`; the
maintainer (xiang90) answered "If there is one in ready, then it is probably fair", but the documentation change
that closed it (etcd-io/etcd#4049) added the "may call Advance while it is applying" permission without that
exception. This PR writes down that answer. etcd-io/raft#80 (open, pav-kv): the conf change checks are "a
collection of tricks", and the configuration should be tracked explicitly; that is the long-term redesign, not
this fix.

## Other candidates

- **`raft-snapshot-during-apply-stale-confchange`** (draft, off c51f010, fix 2425490, no changelog commit and no `AsyncStorageWrites` hold since
  2026-10-23): independent bug (it needs no
  lag: a faithful application, a snapshot stepped between `Ready` and `ApplyConfChange`) and independent fix
  (`handleSnapshot` defers a snapshot while `applying > applied`). The two fit together: that fix's meta says it
  "assumes conf changes are applied before `Advance`, as doc.go's example loop does"; this PR makes that the
  documented rule, so the case it leaves uncovered becomes a misuse. The ranking's "the track patch fixes it too"
  applies to the `track` patch (alternative (b) below), which this candidate does not take, so the snapshot
  candidate is still needed. No conflict: `git merge-tree --write-tree` of this branch with 9dc2d50 (whose `raft.go` 2425490 keeps; not rerun) and with
  `raft-async-snapshot-during-apply-divergence`'s b60b90c is clean (2026-10-23; this PR touches only comments,
  in `raft.go` the `Config.AsyncStorageWrites` one). Not mentioned in either PR (not a split).
- Also clean against `fix/raft-memorystorage-initialstate-unlocked`; against `fix/raft-confstate-unknown-fields-panic`
  and `fix/raft-joint-empty-transition-panic` only their changelog commits conflict, with `main` as well.
- **`etcd-leader-advance-before-applyconfchange`** (etcd-io/etcd, `issues/upstream/etcd-leader-advance-before-applyconfchange/`):
  etcd's leader currently calls `Advance` before `ApplyConfChange` (`server/etcdserver/raft.go`: the leader's
  `Advance` does not wait for the apply goroutine, which applies the conf change later), the order this PR
  documents as not allowed. Investigated 2026-10-23: in etcd the bad execution is possible and no etcd check
  prevents it (two concurrent membership changes can both commit, then a partition gives disjoint quorums), only
  timing does; not reproduced on a cluster. Separate repository, separate PR, on hold: file it after this one is
  accepted (its expectation cites `Node.Advance`'s new sentence). This PR does not mention etcd.

## Why the fix works

What the base does in the test: node 1 leads `{1,2,3}`. "remove 2" is committed at index 2 and handed out in a
`Ready`; node 1's application calls `Advance`, so node 1's applied index is 2, but has not called
`ApplyConfChange`, so its configuration is still `{1,2,3}`. Node 1 proposes "remove 1": the leader's check
`pendingConfIndex (2) > applied (2)` is false, so it is appended at index 3 as a conf change and committed by
`{1,2}` (or `{1,3}`) under `{1,2,3}`. Nodes 2 and 3, which apply before `Advance`, reach configuration `{3}`.
Node 3 cut off, node 1 commits `x` at index 4 with node 2 (quorum of `{1,2,3}`). Node 3 campaigns: no conf change
in `(applied, committed]` = `(3, 3]`, and it is the only voter of `{3}`, so it wins term 2 alone and commits its
empty entry at index 4. Control (temporary edit, not on the branch): with node 1 also applying before `Advance`,
node 1 accepts "remove 1" only after applying "remove 2", ends in `{3}`, drops `x`; index 4 is committed only by
node 3.

The fix states the precondition both guards rely on: a `Ready`'s conf changes are applied before `Advance` (with
`AsyncStorageWrites`: before the `MsgStorageApply`'s responses, the `MsgStorageApplyResp` that moves the applied
index in `appliedTo`, are delivered). Under it, applied index ≥ i implies the configuration reflects every conf
change up to i, which is what `pendingConfIndex > applied` and the scan of `(applied, committed]` assume. The auto-
leave check in `appliedTo` (`newApplied >= pendingConfIndex`) assumes the same; under the lag it only delays leaving
a joint configuration (liveness).

Every place that documents `Advance` was checked: `doc.go` step 4 and `README.md` step 4 (changed), `Node.Advance`
(changed), `RawNode.Advance` (already says "the application has applied and saved progress in the last Ready",
unchanged), `Config.AsyncStorageWrites` (changed: it said nothing about when the apply responses may be delivered
relative to `ApplyConfChange`), doc.go's two example loops (both already call `ApplyConfChange` before `Advance` /
before `send(m.GetResponses())`, unchanged). etcd's `contrib/raftexample` applies conf changes before `Advance`.

## Why the test shows the bug, not a misuse

The reproduction uses `Node` (not `RawNode`, whose `Advance` comment already says "has applied"), whose `Advance`
comment says "as an optimization, the application may call Advance while it is applying the commands", and
doc.go's step 4 says `Advance` "may be done at any time after step 1". Every node persists `HardState` and entries
before sending the `Ready`'s messages (step 2) and applies committed entries in order (`Ready`'s note: none from
the next `Ready` before the previous one's). Nodes 2 and 3 apply before `Advance`; node 1 calls `Advance` and
applies its entries at the end, in order (a slow apply). Proposing a second membership change after the first is
committed is ordinary. The removed node 2 still acknowledges node 1's appends, as raft followers do; doc.go does
not require a removed node to stop. The partition is one cut (node 3 from the others).

The test drives `Node`s through `newNodeTestHarness` (the package's harness for `Node`); `network.send` drives bare
`raft`s, which have no `Ready`/`Advance` cycle. It waits for each `Ready` up to 20 ms; 5/5 runs with `-race` fail
the same way.

## Verification (go1.26.9 linux/amd64, 2026-10-21; rerun 2026-10-23)

2026-10-23: reproduction branch 3dcedb6 fails (`node_test.go:1148`, `expected: "1/4 EntryNormal \"x\""`, `actual  :
"2/4 EntryNormal \"\""`, `index 4 committed on nodes 1 and 3`), `-race -count=5` 5/5 the same way; fix branch
fd30b41 `go test -count=1 ./...` ok, `gofmt -l` empty, `go vet ./...` clean; the fix changes only comments (the
`node.go`/`raft.go` lines are `//`, the `doc.go` lines are inside its package comment block); the test spans
`node_test.go` lines 1063-1150, as the issue links.

- Reproduction branch 3dcedb6af (`go test -count=1 -run 'TestNodeAdvanceBeforeApplyConfChange$' .`): fails,
  `expected: "1/4 EntryNormal \"x\""`, `actual: "2/4 EntryNormal \"\""`; `-race -count=5`: fails 5/5 the same way.
- Fix branch fd30b41a2: `go test -count=1 ./...` (raft, confchange, quorum, raftpb, rafttest, tracker) ok;
  `gofmt -l .` empty; `go vet ./...` clean. The reproduction test still fails on it (documentation only).
- The `Config.AsyncStorageWrites` sentence, checked on `main` with a temporary test (not on any branch): a
  single-voter `RawNode` with `AsyncStorageWrites` commits "add 2"; with the `MsgStorageApply`'s response stepped
  and `ApplyConfChange` not called, a second `ProposeConfChange` ("add 3") is appended as `EntryConfChange` while
  the voters are still `(1)`; with the response held, it is ignored ("possible unapplied conf change at index 2
  (applied to 1)"). So the response, not `ApplyConfChange`, moves the applied index the check reads, as `Advance`
  does (both step the same `MsgStorageApplyResp`, `rawnode.go:384-395`, `raft.go:1206-1211`).
- Not run: `make verify`, golangci-lint.

## If a reviewer asks

Candidate layers and fixes, and why the documentation is the one a maintainer would merge. The root-cause rule
(step 7) asks whether the helper (`hasUnappliedConfChanges`, the leader's `pendingConfIndex > applied`) should be
fixed instead: no, because the defect is the permission, not the check. Under the contract the code was written
for and every example follows, the check is right; making it right under the permission needs raft to see every
`ApplyConfChange` call, which applications that reject or skip conf changes do not make ((b) below).

- **(a) Documentation (taken).** The guards have read the applied index since they were written; every example in
  the package (doc.go's two loops, README's) and `RawNode.Advance`'s comment already apply conf changes first; the
  2016 maintainer answer (etcd-io/etcd#4203) says so. Only `Node.Advance`'s optimization note and step 4's "at any
  time after step 1" promise more. Fixing those two sentences makes the documentation match the contract the code
  and every example implement, without changing behavior for any application.
- **(b) raft tracks which conf changes have been passed to `ApplyConfChange`** (the `track` patch,
  `issues/raft-conf-lag-model/guard-fix.patch`, against 40f8be7: a queue of handed-out conf entry indexes popped
  by `applyConfChange`; `hasUnappliedConfChanges` and the leader's check use it). This is the fix that makes the
  current permission true, and the one the skill's root-cause rule points at (the helper's name,
  "hasUnappliedConfChanges", promises what it does not check). It is not taken because not every caller can
  keep the contract it needs (one `ApplyConfChange` call per handed-out conf entry, in order):
  - `Node.ApplyConfChange` and `RawNode.ApplyConfChange` tell an application that rejects a conf change not to
    call `ApplyConfChange` at all (doc.go says to call it with `NodeId` zero): such an application would leave an
    entry queued forever and its node could never campaign again.
  - etcd, raft's main user, skips `ApplyConfChange` for the conf entries it replays after a restart below its
    consistent index (`server/etcdserver/server.go`, `applyConfChange`, "We don't validate the configuration change
    when `shouldApplyV3` is false, so we shouldn't apply it to raft either"), because its `ConfState` at restart is
    rebuilt from its backend, ahead of raft's applied index. Default-on tracking would leave every etcd member that
    restarts within `SnapshotCount` entries of a membership change unable to campaign.
  So (b) can only be opt-in (`Config.TrackConfChangeApplication` in the prototype: about 150 lines of code and
  480 of tests), which fixes nothing for existing applications and adds a mode to maintain; it is a feature proposal,
  closer to etcd-io/raft#80's redesign than to a bug fix. The documentation fix does not preclude it.
- **(b') An index-carrying `ApplyConfChangeAt(index, cc)`**, letting raft know exactly which entry is applied: new
  API, same adoption problem; recorded in `guard-fix.md`.
- **(b'') raft refuses to move the applied index past an unapplied conf change** (in `appliedTo`): needs the same
  tracking and has the same liveness problem for applications that skip calls.
- **(c) Fix etcd only** (its leader waits like its followers): fixes etcd, not raft's documentation, which keeps
  promising an unsafe order to every other application. Done as well, as a separate etcd PR
  (`etcd-leader-advance-before-applyconfchange`), which this one justifies.
- Why `Node.Advance` keeps its optimization note: it is still right for snapshots and normal entries (applying them
  late is safe: raft never reads the state machine), which is what the note's example (a large snapshot) is about.
- Why also `Config.AsyncStorageWrites`: with asynchronous writes the applied index moves when the
  `MsgStorageApplyResp` is stepped, and with `RawNode` `ApplyConfChange` must run on the goroutine that owns the
  node, not the apply thread; nothing ordered the two. The doc.go example already orders them; the new sentence
  makes it a rule.
- The panic: the same window lets a follower campaign with its own removal committed but not applied; if its
  `ApplyConfChange` comes while it is a candidate and it wins, `becomeLeader` dereferences its missing `Progress`
  (`issues/raft-conf-lag-model/removed_candidate_rawnode_test.go`, reproduced at 40f8be7 through `RawNode`, not
  re-run on `main` and not in the issue). The documentation fix rules it out the same way.
- The inconsistency between doc.go step 3 ("ApplyConfChange must be called one way or the other", `NodeId` zero
  to cancel) and `Node.ApplyConfChange`/`RawNode.ApplyConfChange` ("must not be called" for a rejected change):
  left alone; the new sentences say "apply" (see `ApplyConfChange`), which reads right under either.
- Non-atomic persistence of entries and `HardState` hides a committed conf change from the campaign check after a
  restart (`issues/nonissues/raft-commit-lost-with-entries-kept.md`): a different precondition, not in this PR.

## check.py (2026-10-23)

Run as `python3 -I .claude/skills/upstream-report/check.py raft-advance-before-applyconfchange`, with the
documentation-only shape (one commit changing comments only, the reproduction on `repro/<slug>`): no FAIL. WARNs,
decided:

- The issue's 383 words (aim 380, rewritten free-form with the cause after the 2026-10-23 review): kept; the four
  steps are the shortest execution found (three nodes, one cut).
