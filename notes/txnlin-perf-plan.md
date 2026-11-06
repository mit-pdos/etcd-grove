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

## Decision (2026-11-06, the user, via etcd-grove-82)

Options (2) and (b) of "Go first":

- **(2), a test-only fix to partition's `TestFailover`.** The linearizability check stays over the
  whole history; the workload changes so that fewer writes time out during the blackhole (no writes
  to the cut member during the cut, or shorter timeouts). A check of a history window only if
  neither works, and then only after asking. Bar: 5/5 sequential runs under a 32G memory cap
  (`systemd-run --scope -p MemoryMax=32G`), peak memory recorded.
- **(b), the binary-search `addConfig` only.** (a) (sorted `pend`) and (c) (`Model.Hash`) bought
  nothing on the measured history and are reverted. The model is retranslated and proved
  equivalent to `lean`'s, so that `etcd_txnlin_safe` and the closed theorems through `linkvtxnS`
  keep their statements; no new axiom or `sorry`; an exported statement that must change is a stop.
- k8s/etcd3's copy (`examples/k8s/etcd3/k8setcd3.go`) stays a follow-up after stage 7c.

## (2): TestFailover's workload

The test-only fix of the decision above, in `examples/etcd/partition/linkv3p_test.go`, against
the model at `1f67de4b37` (the binary-search `addConfig`).

### The change

The user's first choice: no writes are routed to the blackholed member.

- **Routing.** A fourth client, `cli23`, connects to members 2 and 3's bridges only. While member
  1 is blackholed (from the run's start until 1s after the unblackhole), every operation but a Get
  or a List goes through `cli23`. That is a put, a delete or a transaction. The reads go through the
  three clients of all three bridges, as before. After that second, writes go through the three
  clients again.
- **`cutRun`.** It takes a `pick func(read bool) int` (nil: random, as before; `TestClientCuts`
  passes nil). It sizes its per-client counts by `len(clis)` and logs the number of failed writes.
- **TestFailover's checks.** Its per-client checks skip `cli23`'s operations (`op.cli == 3`), both
  in the control loop's "every client served" and in the checks after the run.
- **Also.** The warm-up loop is factored out of `cutSetup` (`warmUp`). The import order is now
  gofmt's: it was not gofmt-clean before.

### Why it keeps the test's purpose

Every assertion is unchanged, and each still tests what it did:

- **Phase 1, the failover through the blackholed member, is now shown by reads only.** A read on
  member 1's dead connection is held until its request timeout and fails, as a write was. The
  timeout is the caller's context, and the balancer's pick and the keepalive close are the same for
  every call. So the checks hold as before:
  - stalls only at a request timeout or later;
  - some request timeouts;
  - the last stall after keepalive's first ping (about 15.2 s in every run);
  - every client served after the last stall.
- **What is weakened:** in phase 1, no write goes through the dead connection. A write failing at a
  blackhole and staying pending is still tested:
  - by `TestClientCuts`, through the same `cutRun` and porcupine check;
  - by `TestWriteOnce`, with no double apply;
  - and here, by the cut of members 2 and 3, which fails the writes in flight on their connections.
- **Phase 2, the return to member 1, is shown by reads and writes**, as before.
- **`okAfter[i] > 0` holds by construction.** The control goroutine unblackholes only after every
  client has served an operation started after the last stall, and the check after the run counts a
  superset of those operations. That is why its counts can be low (4-9 per client in runs 2 and 4)
  without risk.

Porcupine's check is still over the whole history. The failed writes are now at most the writes in
flight at the cut of members 2 and 3: 0-1 per run, against 7-10 before.

### TestFailover, 5 runs

The runs were sequential, each with `go test -v -count=1 -run '^TestFailover$'` under
`systemd-run --scope -p MemoryMax=32G --quiet`.
- `/usr/bin/time` is not installed. "Max RSS" is `getrusage(RUSAGE_CHILDREN).ru_maxrss`, which is
  what GNU time's "Maximum resident set size" reports, taken by a wrapper inside the scope.
- "cgroup peak" is the scope's `memory.peak`.

| run | load at start (1 min) | wall | result | failures (reads / writes) | max RSS | cgroup peak |
|---|---|---|---|---|---|---|
| 1 | 25.4 | 87 s | PASS | 9 / 1 | 408 MiB | 488 MiB |
| 2 | 14.5 | 89 s | PASS | 9 / 0 | 429 MiB | 502 MiB |
| 3 | 8.1 | 89 s | PASS | 9 / 1 | 416 MiB | 492 MiB |
| 4 | 8.8 | 92 s | PASS | 9 / 0 | 429 MiB | 501 MiB |
| 5 | 12.0 | 86 s | PASS | 9 / 0 | 411 MiB | 477 MiB |

- **The stalls are the same in every run.** There are 9, all reads that failed at the request
  timeout, three rounds of one per worker: about 0-5 s, 5-10 s and 10-15 s.
- **The phases' times are the same in every run:**
  - member 1 unblackholed at about 20.1 s;
  - members 2 and 3 cut at about 23.1 s.
- **Before this change** the runs passed 3 of 5 under the cap, at 9.4-32 GiB with 7-10 failed writes
  ("TestFailover, 5 runs (the new model)" above).

### The rest of the package

One run of the package's other tests, under the same cap:
- the tests: `TestMemberIDs`, `TestMainRun`, `TestClientCuts`, `TestWriteOnce`, `TestWatchFailover`
  and `TestMainWatch`;
- **all pass**, in 114 s, at load 8.4 at start;
- max RSS 332 MiB, cgroup peak 146 MiB;
- `TestClientCuts` had 3 failed writes.

### Verdict

**The bar is met.** TestFailover passed 5 of 5 runs under the 32G cap, peaking under 0.5 GiB, in
about 90 s each. Porcupine's check is still over the whole history, and no check of a history
window was needed.
