# The restart probe (R2d'a)

A deterministic in-process Go simulation of a 3-member raft v3.7.0 cluster, driven the way etcd's
raft loop drives `raft.Node` (`server/etcdserver/raft.go` at etcd `673da07c8`), to measure how often
the restart-only premises of R2d'a fail in Go runs (`notes/restart-plan.md`, "R2d'a restart-only
premises", and "Hwpend: the Go probe and the narrowing"). Written by the R2d'a session in
`/shared/tmp/winpend-probe` (2026-11-06), copied here unchanged.

It is its own Go module (`go.mod`, module `winpendprobe`, requiring `go.etcd.io/raft/v3 v3.7.0`
upstream, not the fork), outside every tool's reach: `etc/goose.py` translates only its projects'
directories and checks only the go.mod files `GO_MOD_PINS` names; `etc/verified-code.py` reads only
the projects' source directories; CI (`.github/workflows/lean.yml`) and `etc/gates.sh` run `go`
only through `etc/goose.py --check`; `etc/issues-status.py` reads Go tests only under `issues/`.

## What it measures

- **`Hwpend`** (`srvWinPend`, `InvRun.lean`): whether a replay batch's raft term `rt` (etcd's
  `raftTerm`, stamped on each `toApply`) equals the term of a `MsgSnap` this member has sent
  (`TestRandomized`, the "premise fails" line; `TestScenarioA/B/D`, single traces);
- **the snap-term bound** (`rnSnapTermAbove`): `MsgSnap`s sent by restarted incarnations with
  `Term ≤` the restored `HardState` term (`TestZZZ_Totals`);
- **in-window installs** (`rnWinInstallAbove`): snapshot installs at a restarted member inside the
  replay window, against the restored log's last index and against the commit at restart
  (`TestZZZ_Totals`, with the traces of the below/equal cases);
- **the `Ready`-level count**: the replay batches (one per `Ready`), their `rt` histogram (`0`, `= T`,
  `> T`, with `T` the restored term) and the batches failing at apply time (`TestRandomized`).

## The harness and its limits

Per member: `raft.RawNode` over a `MemoryStorage` standing for the WAL and snapshot (persisted
before `Advance`); etcd's `raftTerm` (0 per incarnation, set by every non-empty `HardState`); an
apply loop lagging the raft loop, with snapshots and compaction at scaled-down counts (`SnapCount`
20, catch-up 5); `MsgSnap` to followers lagging past the compaction; kill/restart with `Applied =
0`; PreVote and CheckQuorum on (one mode without PreVote). `TestRandomized` runs 400 seeds of
1500 rounds in three modes: "etcd-like" (the raft loop drains every `Ready`), "slow-handout" (one
`Ready` per round with `MaxCommittedSizePerReady = 1`, one entry per `Ready`) and
"slow-handout-novote" (the same without PreVote).

Limits:
- **The handout is by entry count, not bytes.** Entries are a few bytes, so the etcd-like mode
  never reaches the 1 MB `MaxSizePerMsg` cap etcd's handout splits at (etcd leaves
  `MaxCommittedSizePerReady` unset); the split is only the slow modes' one entry per `Ready`. So the
  etcd-like 0 below **understates** `Hwpend`'s failures: a replay over 1 MB with a snapshot inside
  the window and a mid-replay election fails it with default flags (the R2d'a review, finding 3).
- No realistic `MaxCommittedSizePerReady`, no wall clock (one round = one tick = one message hop),
  no conf changes, no server-side merge, no v2 store, no fsync, no real entry sizes, and
  `SnapshotCount`/catch-up scaled down from etcd's 10000/5000.

## Numbers (2026-11-06)

- `Hwpend`: etcd-like, 0 of about 4250 former-leader restarts fail it; slow handout 2-3% (this
  copy's rerun: 74 of 4266 former leaders, 86 of 5900 restarts), about 3% without PreVote (94 of
  3377, 152 of 5879). Every failing run is elected at `T' > T₀` mid-replay, then sends a `MsgSnap` at
  `T'` (failing batches: `rt > T` all of them, `rt = T` none, the `MsgSnap` always from the same
  incarnation). The old text's proxy fails about 99% (drained) and 49-77% (slow).
- Snap-term bound: 0 of about 7,300 `MsgSnap`s from restarted incarnations (rerun: 0 of 7281) had
  `Term ≤` the restored term.
- In-window installs: about 400 per run (rerun: 412 in the window, 6585 outside); against the
  restored log's last index 23-35 below, 0-4 equal, the rest above (rerun: 25 / 1 / 386); against
  the commit at restart, **0 at or below**. The below/equal cases come only from the restored log's
  uncommitted tail (trace: seed 356).
- `Ready`-level count (rerun): etcd-like 5235 replay batches (`rt` 0: 3614, `= T`: 360, `> T`:
  1261), 0 failing at apply time; slow handout 556333 (1059 failing); slow without PreVote 331174
  (2742 failing).

No etcd or raft bug was found.

## Rerun

```
cd notes/restart-probe && PATH=/usr/local/go/bin:$PATH GOTOOLCHAIN=go1.27.3 TMPDIR=/shared/tmp GOFLAGS=-mod=mod go test -count=1 -v -run 'Scenario|Randomized|ZZZ' .
```

About 25 s. It leaves `go.mod` and `go.sum` unchanged.
