# The lessor's other methods (axiom review, 2026-11-07)

**Reviewed** (axiom sweep batch 3, target B3-2; worktree `axiom/sweep-b3` at `92e61b5070`). The Go
code is etcd's `server/lease` at the etcd pin `673da07c8fab` (the examples module's fork; lines
read in `.lake/go-src/etcd`, at `249d76bea7`, whose `lessor.go`/`lease.go` are identical), with zap v1.28.0, run with
`GOTOOLCHAIN=go1.27.3`.

| axiom | file:line | triple |
|---|---|---|
| `lease.lessor.Promote.wp_proof` | `Proof/go_etcd_io/etcd/server/v3/lease/lessor__Promote.lean:29` | `Spec/.../lease/lessor__Promote.lean:32-37`: pre `lessorInv lp γl ∗ lessorCfg lp`, post `True` |
| `lease.lessor.Demote.wp_proof` | `Proof/.../lease/lessor__Demote.lean:29` | `Spec/.../lease/lessor__Demote.lean:28-32`: pre `lessorInv lp γl`, post `True` |
| `lease.lessor.Stop.wp_proof` | `Proof/.../lease/lessor__Stop.lean:26` | `Spec/.../lease/lessor__Stop.lean:39-44`: pre `lessorStopTok lp`, post `True` |
| `lease.lessor.scheduleCheckpointIfNeeded.wp_proof` | `Proof/.../lease/lessor__scheduleCheckpointIfNeeded.lean:28` | `Spec/.../lease/lessor__scheduleCheckpointIfNeeded.lean:31-42`: `lessorCfg`, `cp`, the checkpoint heap (`queueAt … 1`), the lease's `remainingTTL`/`ttl`; the heap back as some queue |
| `lease.lessorStopTok` (+ `lessorStopTok_timeless`) | `Proof/.../lease/LessorBackend.lean:195-196` | opaque `IProp`; given once by `NewLessor.spec` (`Spec/.../lease/NewLessor.lean:157`) |

## Verdicts

| axiom | verdict |
|---|---|
| `Promote` | **Refuted (Go side; Lean not built)**: panics on a lessor whose logger is the zero `zap.Logger` |
| `scheduleCheckpointIfNeeded` | **Refuted (Go side; Lean not built)**: the same panic, reached through the proved `Grant` (and `Checkpoint`) |
| `Demote` | **Survives** |
| `Stop` | **Survives** |
| `lessorStopTok` | **Survives** |

The refutation is the zap-zero family (`zap-zero.md`, sweep B1-2) showing up one level up.
`NewLessor`'s only premise on the logger is `⌜lg ≠ null⌝`. `lessorCfg` keeps it as
`lF "lg" lp ↦□ lg` with nothing else said (`InvLessor.lean:966-972`). `scheduleCheckpointIfNeeded`
logs through it at Debug (`lessor.go:759-764`) whenever a checkpointer is set and the lease's TTL
is above the checkpoint interval. On `&zap.Logger{}`, `Logger.check` calls `Enabled` on the nil
core (zap `logger.go:331`) and panics. Neither axiom's proof goes through
`zap.Logger.Debug.wp_proof`, because both are names-only. Repairing zap's specs therefore does not
repair these two: the logger fact has to reach `lessorCfg`.

## The counterexamples

`examples/axiomcx/lessormethods/lessormethods.go` (package `lessormethods`):

```go
func newLessor(dir string) (lease.Lessor, backend.Backend) {
	be := backend.NewDefaultBackend(zap.NewNop(), dir+"/db")
	le := lease.NewLessor(&zap.Logger{}, be, noCluster{}, lease.LessorConfig{})
	le.SetCheckpointer(func(context.Context, *pb.LeaseCheckpointRequest) error { return nil })
	return le, be
}

// Promote: a lease of TTL 1000 s (> the default 300 s interval) granted while not primary
// (forever(), nothing scheduled, no log), then Promote(0).
func PromoteZero(dir string) {
	le, _ := newLessor(dir)
	if _, err := le.Grant(1, 1000); err != nil { panic("grant") }
	le.Promote(0)
}

// scheduleCheckpointIfNeeded (through the proved Grant): Promote(0) of the empty lessor
// (no lease, no log), then Grant on the primary lessor (lessor.go:318-321).
func GrantZero(dir string) {
	le, _ := newLessor(dir)
	le.Promote(0)
	if _, err := le.Grant(1, 1000); err != nil { panic("grant") }
}
```

`noCluster`'s `Version()` returns `nil`, which meets `clusterOk`. The checkpointer does nothing, so
the opaque `ckptEffectsOk` (a premise of `NewLessor`) holds of this program. It is never called
anyway: the panic comes first.

**Runs.** `LESSORMETHODS_RAW={promote,grant} go test ./axiomcx/lessormethods/ -run TestRaw`, each
10 times in separate processes (raw logs `/shared/tmp/7c-logs/b3-2-runs-{promote,grant}.log`):
**promote 10/10, grant 10/10** panicked. The traceback
(`/shared/tmp/7c-logs/b3-2-raw-*.log`) is:

```
panic: runtime error: invalid memory address or nil pointer dereference
go.uber.org/zap.(*Logger).check            zap@v1.28.0/logger.go:331
go.uber.org/zap.(*Logger).Debug            zap@v1.28.0/logger.go:238
lease.(*lessor).scheduleCheckpointIfNeeded lease/lessor.go:760
lease.(*lessor).Promote                    lease/lessor.go:491     (GrantZero: lease.(*lessor).Grant lessor.go:320)
lessormethods.PromoteZero                  lessormethods.go:43
```

`TestPromoteZero` and `TestGrantZero` (recovered) pass on every run.

### Lean sketch (not built)

The statement: `ckptEffectsOk → {{ isPkgInit lessormethods ∗ <backend premises> }} @!
lessormethods.PromoteZero #dir {{ RET #(); True }}`, and the same for `GrantZero`.

1. **The backend.** `backend.NewDefaultBackend` has no spec, so the program should instead call
   the one whose proved spec gives `isBackend`, `bOpen`, `wbTok` and `rbPart` (`backend.New`,
   `Spec/.../backend/New.lean`, which is proved over bbolt's axioms). This is where the
   counterexample picks up axioms that are not under review: bbolt's `Open_kv` and the file-system
   environment premises. `New` leaves the `lease` bucket absent, which meets `NewLessor`'s
   `(r.lookup "lease").getD ∅ = ∅`.
2. **The logger.** `wp_alloc` the zero `zap.Logger` (its type and instances are translated and
   proved, `zap-zero.md`), which gives `lg ≠ null`.
3. **`NewLessor`.** `wp_apply lease.NewLessor.wp_proof` with `GA := fun _ => True`,
   `mono := true`, `S := (· = "lease")`, and the hypothesis `ckptEffectsOk`. This gives
   `lessorInv`, `lessorCfg`, `lessorCkptOk l`, `leaseOwn γl [] ∅`, `leaseEver γl []`,
   `leaseRevokers γl []`, `lessorApplyOk lp` and `lessorStopTok`.
4. **`SetCheckpointer`.** Call it through the interface by `lessorCkptOk` (any `cp`, returns).
5. **`PromoteZero`.**
   - `Grant` (proved, `lease.lessor.Grant.wp_proof`). Its backend contract comes from
     `lessorApplyOk`, as the server's apply does. Its proof uses the `scheduleCheckpointIfNeeded`
     axiom but does not call it here: the lessor is not primary. It also uses the prometheus
     `Observe`/`Inc` axioms and `persistTo`'s backend specs.
   - The interface call `Promote` reduces to the method, as `LessorOk.lean:90-96` does.
     `wp_apply lease.lessor.Promote.wp_proof` with `lessorInv ∗ lessorCfg`.
   - Return.
6. **`GrantZero`.** Apply the `Promote` axiom (empty lessor), then `Grant`'s proved spec. On the
   primary lessor, `Grant` reaches the `scheduleCheckpointIfNeeded` axiom (`Link.lean:1173`, used
   at `:2470`). Discharge the `if err != nil { panic }` from `Grant`'s post: `id = 1 ≠ 0`,
   `1000 ≤ MaxLeaseTTL`, `1 ∉ []`.
7. **`#print axioms`.** It should show the axiom under review plus `NewLessor`'s, bbolt's/the
   backend's, prometheus's, and the generic ones. None of those carries the panic: it is inside
   `Promote`/`scheduleCheckpointIfNeeded`, which are names-only. So the counterexample is not
   "clean" in the skill's strict sense, but the extra axioms are about the setup.

**Reach** (the plan's counts, `notes/axiom-sweep-plan.md` B3-2: 37-41 roots, 17 `*_safe`). By grep:
- `Promote` reaches the server through `lessorOk_of_lessorInv` (`etcdserver/Results.lean:1189`,
  `:2112`; `LessorOk.lean:78-96`).
- `scheduleCheckpointIfNeeded` reaches it through `Grant` and `Checkpoint`
  (`etcdserver/Link.lean:2470`, `:2474`).

The server passes `cfg.Logger`, a real logger. So etcd is not affected: like zap-zero, this is a
premise gap.

### Restatement (applied 2026-11-10, `dbe4904326`, with the pre's `⌜lg = null⌝ ∨ zapLoggerOk lg` as the user decided on 2026-11-07; first proposed as below)

Take zap-zero's repair (a constructor-given persistent `zapLoggerOk lg`, sweep repairs 1) and carry
it into the lessor:
- `NewLessor.spec` takes `zapLoggerOk lg` in place of `⌜lg ≠ null⌝`;
- `lessorCfg` holds `lF "lg" lp ↦□ lg ∗ (⌜lg = null⌝ ∨ zapLoggerOk lg)`, since Go tests
  `le.lg != nil`.

`Promote`, `scheduleCheckpointIfNeeded`, `Grant` and `Checkpoint` then read the fact from
`lessorCfg`, and their statements are unchanged. `NewServer`'s logger premise (zap-zero's
`cfg.Logger`) supplies it.

## Attacks that failed

| # | attack | why it fails |
|---|---|---|
| 1 | **`Demote` before any `Promote`, `Demote` twice** | `close(le.demotec)` only if non-nil, and it then sets `nil` (`lessor.go:546-549`). `TestOrders`: no panic |
| 2 | **`Promote` twice** | It makes a fresh `demotec` without closing the old one (`:484`). That is no panic. A `Renew` that captured the old channel for an expired lease (`:404`, `:415-428`) then waits for `revokec` or `stopC`: a wait, not a counterexample. `TestOrders`; `TestConcurrent` needed `Stop` to release such Renews |
| 3 | **Interleaving with `Grant`/`Checkpoint`/`Renew`/`Lookup`/`Leases`/`Remaining`/`Demoted`**: 3000 random apply ops (Grant, Checkpoint, Promote ±1 s, Demote), concurrent Renews and readers, `CheckpointInterval` 1 ms so `runLoop` checkpoints, expiries drained | Everything is under `le.mu`, and `expiry` is also under `expiryMu` (`lease.go:84-96,117-124`). `-race`, `-count=10` (`/shared/tmp/7c-logs/b3-2-concurrent10.log`): no panic, no race report. `Revoke` was not interleaved: its spec needs the watchable store's range deleter (`rdIs`), so it is outside a lessor-only program (see the Go note below) |
| 4 | **Overflow in `Promote`**: `extend` = `MaxInt64`/`MinInt64`/−1 h/`MaxLeaseTTL` s; `Checkpoint(id, MaxInt64)` and `MinInt64` then `Promote`; 1200 leases (≥ `leaseRevokeRate` 1000) so that the sort and float window loop run; TTL `MaxLeaseTTL` | `refresh` computes `extend + Duration(rTTL)*Second`, which wraps silently, and `time.Time.Add` does not panic. `time.Duration(rateDelay)` of a huge or infinite float is implementation-defined, with no panic. `sort.Sort` with a time-varying `Less` stays in bounds. `TestExtremes`, `-race`: no panic |
| 5 | **`targetExpiresPerSecond = 0`** (`(3*rr)/4` with `rr ∈ {1}`) → float division by 0 | A float divide does not panic. Also, `leaseRevokeRate` is unexported, so a client's `LessorConfig` always has 0, which is defaulted to 1000 (`:222-224`). `lessorCfg`'s `0 < rr` (B4b) is the premise that matters, for `leases[0]` |
| 6 | **`scheduleCheckpointIfNeeded` with `CheckpointInterval` −1 h, 1 ns, 0 (defaulted), `MaxInt64`** | `int64(Seconds())` is a float conversion with no panic. `heap.Push` keeps `queueAt`'s indices (`LeaseQueue.Push`/`Swap`, `lease_queue.go:31-46`). `TestExtremes` with `runLoop` running: no panic |
| 7 | **`scheduleCheckpointIfNeeded` reads `lease.ID` without a points-to in its pre** | `ID` is never written after `NewLease`/`initAndRecover`, and every caller holds `ID ↦□` (`leaseMeta`). An exported-field write by a client (`l.ID = …`) needs a write permission that `↦□` denies, and in Go it would only be a race. The method is unexported, so it is reachable only through `Grant`/`Checkpoint`/`Promote` |
| 8 | **The notifier heap through `Promote`** (`RegisterOrUpdate` of fresh items; `m`/`queue` agreement, which `Len`/`Peek` rely on, `lease_queue.go:96-105`) | One item per lease id (the map's keys are the leases' `ID`s). An old item is `Fix`ed at its `index`, a new one pushed: this matches the proved `RegisterOrUpdate`. `Demote` replaces both heaps with fresh ones (`:689-697`), and nothing else keeps a pointer to the old ones |
| 9 | **What the specs frame**: does `Promote`/`Demote` write memory outside `le.mu` that another spec owns or keeps `↦□`? | They write `demotec`, the notifier, the checkpoint heap, each lease's `expiry` (both halves: `leaseMeta`'s under `le.mu`, `leaseExpiry` under `expiryMu`, taken by `refresh`/`forever`) and fresh `LeaseWithTime`s. `grep` finds no `↦□` of `expiry`, `demotec`, `leaseExpiredNotifier` or `leaseCheckpointHeap` outside the lock's predicates. `remainingTTL`, `ttl` and the maps are only read |
| 10 | **`Stop` twice** | It panics (close of a closed `stopC`, `TestStopThen`), but the second call has no `lessorStopTok`. The token is opaque, given once by `NewLessor`, and threaded linearly: `NewServer` → `srvStop.cleanupPart` (`StopApi.lean:54-56`) → `Cleanup`'s pre. No axiom or lemma duplicates it or makes it persistent (`grep lessorStopTok`: 5 files) |
| 11 | **`Stop`, then every method** (`Promote`, `Grant`, `Checkpoint`, `Renew`, `Demote`, `Leases`) | No method uses `stopC`/`doneC` except `Renew`'s wait (`:426`) and `runLoop`. `TestStopThen`: no panic |
| 12 | **`Stop`'s `<-le.doneC`** | `runLoop` closes `doneC` on return (`:621`). If it is stuck in `le.cp(…)`, `Stop` blocks: partial correctness |
| 13 | **Can `lessorStopTok` be realized?** (opaque `IProp` with a `Timeless` instance) | It is consistent: model it as an exclusive token keyed by the fresh `lp` (a location's meta token), allocated in `NewLessor`'s realisation |
| 14 | **A real logger** (`zap.NewExample()`, Debug on) | No panic (`TestOrders`, `TestExtremes`). Only a broken logger refutes |

## Not tried

- **A logger with a panicking core or hook** (`zap.New(core, zap.Hooks(...))`). There is no spec for
  `zap.New`, and the zero logger already refutes.
- **The same zero logger in `runLoop`'s `findDueScheduledCheckpoints`** (`lessor.go:798`, Debug),
  which would refute `NewLessor`'s forked loop. Every checkpoint item is pushed by
  `scheduleCheckpointIfNeeded`, which panics first, so the loop never reaches it.
- **A panicking checkpointer `cp`** (`runLoop` → `checkpointScheduledLeases` `:679`, `Renew`
  `:436`). `lessorCkptOk` accepts any `cp`, but that is `NewLessor`'s and `ckptEffectsOk`'s domain
  (`lease-grant-lessor.md`), not these axioms'.
- **`Demote` proved instead of assumed.** Its proof header says only the close right of `demotec`
  is missing. That is a proof task, not an attack.

## Go-code note (not filed)

`Revoke` with no range deleter set (`le.rd == nil`) returns after its deferred `close(l.revokec)`
without deleting the lease from `leaseMap` (`lessor.go:331-339`). A second `Revoke` of the same id
then panics with "close of closed channel" (`TestRevokeTwiceNoRd`). etcd always sets the deleter
(`mvcc.New` → `SetRangeDeleter`), and `Revoke.spec` requires `rdIs rd …`, so neither etcd nor the
proof is affected. It is a candidate `nonissues/` entry (a precondition etcd meets).
