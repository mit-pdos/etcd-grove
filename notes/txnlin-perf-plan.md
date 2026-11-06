# txnlin-perf: the linearizability check of txnlin's model

Partition's `TestFailover` (`examples/etcd/partition/linkv3p_test.go`, the `lintest.Run` with check
timeout 0 at `:321`) ran past its deadline about 1 run in 2. Its workload takes about 82 s; the rest
of the time goes to porcupine checking the history against txnlin's model
(`examples/etcd/txnlin/linkvtxn.go`: `mcfg`, `state`, `addConfig`, `removeAt`, `closure`, `step`,
`Model`). The diagnosis is in `notes/lease-mono3-plan.md` ("Fails, and not because of R1"), with
evidence in `/shared/tmp/t1-diag/`.

## Go first (2026-11-06)

Branch `txnlin-perf` (worktree `/shared/etcd-grove-txnlin`), off `lean` `3f9a18065c`. This stage
changes Go only: no Lean, no spec, and no regenerated translation. `Code/.../txnlin.lean` is now
stale against the Go (`etc/goose.py --check` would fail), so the Lean model, its translation and
its proof follow in a later stage, if this one is adopted.

### Scope: the four costs

- (a) `pend` is an ordered list. `step` prepends to it, so the same pending set in another order is
  a different configuration.
- (b) `addConfig` dedups by a linear scan, so a step costs about |state|².
- (c) `Model.Equal` is order-sensitive list equality, and there is no `Hash`, so porcupine's cache
  misses.
- (d) `closure` re-explores configurations that are already closed, on every step.

This cost cannot be removed: different application orders of the pending writes give different
stores, through mod revisions.

Approved for measurement: (a)-(c) only. (d) is to be tried only if (a)-(c) fail the bar, and only
after a report.

### The change (commit `cdca003258`)

- **Pending writes sorted.** `pend` is kept sorted under a total order on `Input` (`cmpInput`, field
  by field). `step` inserts a failed write in order (`insertInput`; duplicates kept, since `pend` is a
  multiset). `removeAt` keeps the order. `closure` skips a pending write equal to the one before it.
- **State sorted.** A state is kept sorted under `cmpConfig` (the store, then `pend`), without
  duplicates. `addConfig` is a binary search plus an insertion, in a sorted list, not a map. With
  this canonical form, `Equal`'s list equality is set equality.
- **`Model.Hash`.** An FNV-1a hash of the canonical form (`hashState`).
- **Style.** Goose-style Go: loops and slices, no generics, no `sort` package. String `<`, which the
  model already uses in `setKey`, and string indexing in the hash. It is not translated in this stage.

`examples/etcd/txnlin/perf_test.go` keeps the old model verbatim, renamed `oldModel`.
- `TestPerfHistory` replays a saved history (`TXNLIN_HIST`; `TXNLIN_MODELS=new|old` runs one model;
  `TXNLIN_OLD_TIMEOUT`).
- `TestOldNewDifferential` compares the two models on random histories.

**The saved history.** `/shared/tmp/t1-diag/hist3.gob` was written by a diagnostic overlay of
`lintest.go` (`/shared/tmp/t1-diag/overlay/`, used with `go test -overlay`). With `LINTEST_DUMP` set,
it gob-encodes the `[]porcupine.Operation` just before `porcupine.CheckOperationsTimeout`. To
decode it, `gob.Register(txnlin.Input{})` and `gob.Register(txnlin.Output{})`, then decode into
`[]porcupine.Operation`. It holds 36000 operations, 11 of them failed (8 failed writes).

### Numbers: hist3.gob, old model against new

Measured with porcupine's `CheckOperationsTimeout`, and `Step` wrapped to count calls and size
states. The first pair ran uncapped, with load average 11-18 on 32 cores.

| model | verdict | check time | Step calls | steps/s | peak \|state\| | peak k | peak memory, 32G cap |
|---|---|---|---|---|---|---|---|
| old | Ok | 388.5 s | 58414 | 150 | 1668 | 7 | killed at the cap after 244 s (32.0 GiB) |
| new | Ok | 129.6 s | 58414 | 451 | 1668 | 7 | killed at the cap after 105 s (32.0 GiB) |

- **The verdicts agree** (Ok).
- **The speedup is 3.0x, all from (b).** The step count and the peak |state| are identical. On this
  history, (a) and (c) merge nothing:
  - every configuration's `pend` was built by prepending in history order, so they all share one
    order already;
  - the closure already holds every application order.
- **Each step still costs about |state| · k · log |state|.** That is `closure`'s full re-exploration,
  (d).
- **Memory is the new limit, the same for both models.** Porcupine keeps every accepted state, in
  its cache and on its `calls` stack. With |state| up to 1668 configurations, each with up to 7
  pending `Input`s (about 270 bytes each), and 58k states, this history needs more than 32 GiB
  under either model. The new model reaches the cap sooner only because it is faster.

### The differential test

`TestOldNewDifferential` ran 5000 random histories of 2-24 operations: `robust_test.go`'s
`randomHistory`, where a sixth of the calls fail and half the histories have one corrupted output.
- The models agree on every one: 4302 legal, 698 illegal.
- 3359 of the histories have failed writes, at most 7 in one history.

txnlin's own tests pass with the new model: `TestModel`, `TestDifferential` (20000 histories
against etcd's robustness model), `TestMainRun`.

### TestFailover, 5 runs (the new model)

`go test -count=1 -run '^TestFailover$'` in `examples/etcd/partition`, one run at a time, with the
default 10-minute timeout. The child gets 9m30s.

**Memory cap.** The runs are capped at 32G (`systemd-run --scope -p MemoryMax=32G -p
OOMPolicy=continue`) at the coordinator's request, after two earlier, uncapped runs reached 26-34
GB beside other sessions' builds:
- the first was killed by the kernel's OOM killer at 560 s, during a full `lake build` of another
  worktree at load average 36-113;
- the second I killed at 34.5 GB RSS.

**Peak memory.** "cgroup peak" is the scope's `memory.peak`; "max RSS" is the largest process's
(`getrusage(RUSAGE_CHILDREN)`).

| run | load at start → end | wall | result | max RSS | cgroup peak |
|---|---|---|---|---|---|
| 1 | 2.8 → 37.5 | 723 s | **FAIL**: at the cap from about 2 min on (653190 `max` events, no OOM kill), until go test's 10-minute timeout (SIGQUIT) | n/a (process timed out) | 32.0 GiB |
| 2 | 37.5 → 33.4 | 119 s | PASS (the run took 1m54s) | 9.1 GiB | 9.4 GiB |
| 3 | 33.4 → 37.6 | 136 s | PASS (2m11s) | 11.6 GiB | 11.7 GiB |
| 4 | 37.6 → 29.5 | 278 s | **FAIL**: the child was OOM-killed at the cap | 31.9 GiB | 32.0 GiB |
| 5 | 29.5 → 9.1 | 151 s | PASS (2m26s) | 29.0 GiB | 29.1 GiB |

- **Time is no longer the problem.** A run that fits in memory now takes 2-2.5 minutes, against
  the earlier 430-575 s.
- **Memory is the problem, and it is not load-dependent.** Peak memory comes from the writes that
  fail while member 1 is blackholed, and from how many of them are pending at once, not from their
  count alone:
  - run 2: 11 failures, 7 of them writes, 9.4 GiB;
  - run 3: 13 failures, 10 writes, 11.7 GiB;
  - run 5: 12 failures, 8 writes, 29.1 GiB;
  - hist3: 11 failures, 8 writes, k up to 7, more than 32 GiB.

  The load (3-38) did not decide any outcome. The first uncapped run's OOM kill was the machine's
  memory, not a deadline.

### Verdict

(a)-(c) **do not meet the bar.** TestFailover passed 3 of the 5 runs under the 32G cap.
- The check is 3x faster, all from (b): (a) and (c) merge nothing on these histories.
- What fails now is memory, under the old and the new model alike: porcupine retains every state,
  and a state holds up to 1668 configurations of up to 7 pending writes each.
- (d) would speed up `closure` but would not shrink the states, so it would not fix the failures.

What would fix them (not tried; each needs approval):
- **Smaller states.** Share the configurations' `pend` lists: they are all suffixes or subsets of
  one sorted list, so a bitmask over the failed writes recorded so far would do. Intern the stores.
  This cuts the per-configuration footprint from about 2 KB to tens of bytes.
- **Fewer failed writes in the test.** Fewer writes timing out during the blackhole, or a check of
  a history window, is a test design change.
