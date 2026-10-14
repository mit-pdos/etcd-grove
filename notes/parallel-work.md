# Parallel work: what another Claude Code session could do now (2026-10-14)

Written by the session driving branch `worktree-raft-rest` (the "integration session"),
for a second session that the user may start to speed things up. Nothing here is started.
Read `CLAUDE.md`, then `notes/STATUS.md` (its first sections: reconfiguration stages 0, D,
L, A1, A2; leader transfer; read-index) before picking a task.

## Where things stand

- Branch `worktree-raft-rest` (pushed to `origin`), head `f5381ef21` when this was written.
  Full build: `lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results
  Proof.github_com.mit_pdos.etcd_grove.examples.register.Results
  Proof.github_com.mit_pdos.etcd_grove.examples.register.Adequacy`;
  `etc/tcb-report.py --check` = 75 axioms, 10 sorries.
- Update 2026-10-14 (head `b2ee06944`): stages A3 and B1 have merged; tasks 1-3 below are done
  (`parallel/b1-review`, `parallel/raft-guard-fix`, merged). Stages B2-B4 merged (`a1b15d409`); **stage B5 is now running**
  (dynamic-mode safety: a dynamic ghost mode, `ownRaftGhost_stepR`, the three overlap cases) in the integration
  session: it edits `Protocol/*.lean` (also `StepR`, `StepRInv`, `RefinementR`), and `Proof/go_etcd_io/raft/v3/Protocol/*.lean` (`Refinement`,
  `StepGhost`, `Ghost`, `GhostState`, `LeaderCompleteness`, `ReadIndex`, `Facts`, `StepC`) and
  the ghost-update boundary in `raft__Step.lean`, possibly `Link.lean`. Avoid those files.
- Next on the critical path (integration session, sequential): B2 (ghost layer on
  `StepC` at a constant configuration) → B3 (model fields, guards, invariants I1–I3) →
  B4 (winners table, configuration-carrying predicates, static mode) → B5 (safety under
  changing configurations) → B6 (read index) → B7/B8 (code connection, snapshots). The plan
  is summarized in STATUS ("Reconfiguration, stage A2" and later sections) and will be
  written out in `notes/reconfiguration-safety.md` by B1.

## Tasks a parallel session can take now (independent of A3 and B1)

Each is self-contained; pick one or more. They avoid the files above.

1. **Upstream drafts for the two safety findings.** `issues/raft-advance-before-applyconfchange.md`
   (reproduced: `issues/raft-conf-lag-model/leaderlag_test.go`) and
   `issues/raft-commit-lost-with-entries-kept.md` (abstract model only). Write issue texts
   for etcd-io/raft in the format of the etcd drafts listed in `issues/README.md`
   (summary, what happens, how to reproduce, expected, the fix): one asking to document
   the precondition (apply a `Ready`'s conf changes before `Advance`; persist entries and
   `HardState` atomically), one proposing the guard fix (task 2). Also note etcd's own
   leader path (`etcdserver/raft.go`, `server.go`: `Advance` without waiting for apply) as
   a possible etcd issue, unconfirmed. Do not file anything; the user files by hand.
   Deliverable: new files under `issues/` and README rows.
2. **Prototype the raft guard fix, with a test.** In a scratch copy of the pinned raft
   (`.lake/go-src/etcd-raft`, do not modify the checkout): make `hasUnappliedConfChanges`
   and the leader's pending check (`raft.go:990`, `1313`) use the index of the last
   configuration actually applied (`ApplyConfChange`) instead of `raftLog.applied`. Show
   `leaderlag_test.go` no longer reproduces the violation (flip its assertion), that
   `go test ./...` passes, and think through async-storage mode
   (`MsgStorageApplyResp`). Deliverable: a patch file and notes under
   `issues/raft-conf-lag-model/`, linked from the issue file.
3. **Adversarial review of B1's paper proof** (`notes/reconfiguration-safety.md`, merged
   2026-10-14 as `bfa867336`; its five repairs and B2's first steps end its report). Read it
   against the Go code (`.lake/go-src/etcd-raft`) and try to break it: the winners table
   and win-time election safety, the commit-fact witnesses and their well-foundedness,
   the generalized leader-completeness case analysis, read index with joint quorums,
   snapshots/compaction (`base > applied`), pre-vote and `MsgTimeoutNow` campaigns,
   auto-leave, a leader's step-down on removal. A counterexample (ideally a Go test, else
   an extension of `issues/raft-conf-lag-model/model.py`) is the most valuable outcome.
   Deliverable: `notes/reconfiguration-safety-review.md`.
4. **Diagnose the flaky parallel build of `stepLeader.lean`.** Under a parallel full
   build it sometimes fails ("unknown free variable", at varying lines around 436/711/813)
   and passes when rebuilt alone. Find the cause (memory pressure? `maxHeartbeats`/
   `maxRecDepth`? nondeterministic elaboration in `iframe`/`wp_auto`?) with your own
   worktree and build cache. Deliverable: a diagnosis and a proposed fix in
   `notes/` — do not edit `stepLeader.lean` while A3 runs (hand the fix back).
5. **Model-check the reconfiguration design more deeply.** The Python model
   (`issues/raft-conf-lag-model/model.py`) only searched to depth 10–11, too shallow to
   separate the faithful and lagging modes. A faster checker (Go, or TLC on etcd-raft's
   `tla/etcdraft.tla` extended with an applied index distinct from the configuration
   switch) that reaches the depth of the known counterexamples (~22–26 steps) and then
   searches the faithful mode exhaustively at small bounds would back B1's paper proof.
   Deliverable: the checker under `issues/raft-conf-lag-model/` and results in a notes file.

## Tasks open since A3 merged (avoid B2's files above; these are in the code layer)

- `getStatus`/`RawNode.Status`/`node.Status` (`Config.Clone`'s spec needs canonical
  learner sets; `node.run`'s status channel is unused today).
- A forwarded `MsgTransferLeader` at the node layer (needs a ghost fact that a follower's
  leader led its term; `raft.Step`'s `RestMsgOk`).
- Learners at the RawNode/node layers: adding a learner (`CCApplies`'s bound), a node that
  is itself a learner (`ownRawNode`'s `id ∈ γ.reCfg`), a learner receiving a snapshot.

## How to work and hand back

- Work in your own git worktree off `worktree-raft-rest` (seed `.lake/` by copying the
  integration worktree's `.lake/build` and `.lake/packages`, so builds are incremental).
- Commit on your own branch; push it to `origin` under a name like `parallel/<task>`;
  never push to `main`/`master` or to `worktree-raft-rest`. Tell the user the branch name
  and a short report; the integration session merges.
- Same rules as the rest of the repository: no new `sorry`/axiom without saying so;
  record Go bugs in `issues/`; run `etc/tcb-report.py --check` if you touched proofs.
