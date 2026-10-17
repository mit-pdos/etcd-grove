# etcd-io/raft#140: tests, fix variant and logs

Report: `../raft-140.md`. Every Go file is a `_test.go` of package `raft`, written for this
verification. Copy it into the root of a raft checkout at the revision given below and run
`go test -run '^<Name>$' -count=1 .` (with `GOTOOLCHAIN=go1.27.1` if the default `go` is
older). A test "fails" when it shows the problem: each asserts the behavior that should hold.

The revisions are:
- **PR head**: etcd-io/raft `ffbd5f78545ac5f26ad23f1071c1133cd2d99251`
  (`git fetch https://github.com/etcd-io/raft pull/140/head`).
- **upstream base**: etcd-io/raft `026484c68b7bc59cd208e216d35e1ff747d24d9c` (the PR's merge base
  with main).
- **fork + PR**: `upamanyus/etcd` branch `pr-raft-140-goose-lean`, commit `726078878` (not
  pushed; in `~/etcd`). This is the pinned v3.7 plus the PR, and it is the code that was verified.
- **fork base**: `upamanyus/etcd` `raft37-goose-lean`, `509271dac` (the pin in `etc/goose.py`).

| File | Test | Revision | Result (log in `logs/`) | Shows |
|---|---|---|---|---|
| `upstream-pr-head/logsynced_repro_test.go` | `TestLogSyncedStaleTail` | PR head | FAIL: "committed entry 4 has term 2; the leader's entry 4 has term 3" (`pr-head-TestLogSyncedStaleTail.log`) | finding 1, locally: an accepted `MsgApp` that ends before a stale tail sets `logSynced`, and a heartbeat commits the tail |
| `upstream-pr-head/logsynced_bogusack_repro_test.go` | `TestLogSyncedBogusAckStaleTail` | PR head | FAIL: "follower committed entry 4 of term 3; the leader's (committed) entry 4 has term 4" (`pr-head-TestLogSyncedBogusAckStaleTail.log`) | finding 1 with raft's own leader (written by the reviewer) |
| `fork-v3.7/bogusack_repro_test.go` | `TestLogSyncedBogusAckStaleTail` | fork + PR | FAIL: "follower committed entry 4 of term 3; the leader's entry 4 has term 4" (`fork-pr-TestLogSyncedBogusAckStaleTail.log`) | the same, on the verified code |
| `upstream-pr-head/logsynced_fuzz_test.go` | `TestLogSyncedFuzz` (`FZ_SEEDS=3000`) | PR head | FAIL: "follower 3 (logSynced, term 13) entry 6 term 9, leader 2 term 10" (`fuzz-pr-head-3000.log`; an earlier run, `fuzz-pr-head-seed37.log`) | finding 1 under a randomized lossy, reordering, crashing cluster (written by the reviewer). Not seed-reproducible: raft's election timeouts use the global random source |
| `upstream-pr-head/leaderhb_repro_test.go` | `TestLeaderHeartbeatCommitUnmatched` | PR head | FAIL: "heartbeat to 2 carries Commit 2 > Match 0" (`pr-head-TestLeaderHeartbeatCommitUnmatched.log`) | finding 2: the leader now sends `Commit > Match` |
| `upstream-base/mixedversion_repro_test.go` | `TestOldFollowerUnmatchedHeartbeatCommit` | upstream base | FAIL: "committed entry 4 has term 2; the leader's entry 4 has term 3" (`up-base-TestOldFollowerUnmatchedHeartbeatCommit.log`) | finding 2: an old follower given that heartbeat commits a stale tail, with no panic |
| `upstream-pr-head/restart_repro_test.go` | `TestRestartedFollowerLearnsCommitFromHeartbeat` | PR head; upstream base | FAIL at the PR head: "follower committed = 3 after 5 heartbeat rounds, want 4"; ok at the base (`pr-head-…`, `up-base-…` logs) | finding 3: the liveness regression |
| `fork-v3.7/restart_repro_test.go` | `TestRestartedFollowerLearnsCommitFromHeartbeat` | fork + PR; fork base | FAIL with the PR, ok on the base (`fork-pr-…`, `fork-base-…` logs) | the same, on v3.7 |
| `fork-v3.7/staleack_repro_test.go` | `TestStaleTermAppRespRegressesNext` | fork base (and fork + PR) | FAIL: "Progress[3] = StateReplicate match=0 next=5 inflight=1" (`fork-base-…`, `fork-pr-…` logs) | the existing-code issue `issues/raft-stale-term-appresp-ack.md` |

The three `fork-v3.7` files can be copied together. Their helpers are named differently (`u64p`,
`p64`/`ent`, `q64`).

## The fix variant

`fix-logsynced-at-lastindex.diff`: against the PR head's `raft.go`, it sets `logSynced` only
when the accepted append reaches `lastIndex()`. The reviewer tried it. Apply it with
`patch -p1 < fix-logsynced-at-lastindex.diff` in a checkout of the PR head. With it:

- `go test ./...` passes (`logs/package-tests-with-fix.log`).
- `TestLogSyncedFuzz` with `FZ_SEEDS=3000` passes (`logs/fuzz-with-fix-3000.log`).
- `TestLogSyncedStaleTail` and `TestLogSyncedBogusAckStaleTail` stop at their "logSynced =
  false" check (`logs/fix-repros.log`). The schedule no longer sets the flag, so the stale tail
  is never committed.

It is not verified. The report proposes the `syncedIndex` variant as the one the existing
proof invariants support.

## Tools

`tools/lake-build-errors.sh`: the wrapper used for the Lean builds of this branch. It runs
`lake build` with the shared artifact cache and prints only the errors. The worktree path in it
is this branch's worktree.
