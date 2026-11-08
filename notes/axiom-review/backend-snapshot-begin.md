# The backend's open snapshots and bbolt's read transactions: `Snapshot` and `Begin_kv`'s counts

**Reviewed (2026-11-06, `lean` at `574d6ff14b`; branch `axiom/backend-snapshot-begin`):**

- `bbolt.DB.Begin_kv.wp_proof` (`Proof/go_etcd_io/bbolt/DB__Begin_kv.lean:24`, its triple in
  `Spec/go_etcd_io/bbolt/DB__Begin_kv.lean`), with the triples a program needs around it:
  `Open_kv`, `DB.Close_kv`, `Tx.Rollback_kv`.
- `backend.backend.Snapshot.wp_proof` (`Proof/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean:66`),
  with `snapshot.Close` and `backend.Close`.

The question is the bound and count claims only: what limits the open read transactions and
snapshots. The earlier reviews covered the rest and are not redone: `snapshot.md` (the observation
`Q`), `backend-snapshot-fk.md` (the `fkRd` post), `bbolt.md` (the other `_kv` claims). This review
starts from `notes/bounds-plan.md`, "Known gap: the backend's open snapshots and read transactions".
That gap came from `authrdn-count.md`'s attack 8.

**The other backend and bbolt trust-boundary specs.** The search below found none that carries a
reader slot, the `2 ^ 28` pool, `rdStockN` or a transaction count:

- `etc/bounds-check.py --kind` for `spec-thread`, `spec-readers`, `stock` and `spec-receipt`;
- a grep of the 29 axiomatized specs under `Spec/go_etcd_io/bbolt/` and `.../storage/backend/`
  for `rdTok`, `threadTok`, `bkRPool`, `rdStockN`, `actualMaxReaders`, `threadPool` and `wbTok`.

`Snapshot` is the only one that takes any token: `wbTok`, one write-back's budget, out of
`wbInit = 2 ^ 40 − 1`. The backend's `rdStockN` matches are all in proved specs (`mvcc`,
`etcdserver`), over verified RLock tokens; `authrdn-count.md` checked their partition.

**Still axioms after the bbolt-v2 merge.** Both targets, and all 20 `_kv` triples. bbolt is now
translated with bodies (`Code/go_etcd_io/bbolt.lean`: `DB.Begin.impl`, `DB.beginTx.impl`,
`DB.removeTx.impl`, with `mmaplock` a translated `sync.RWMutex`). Its own API spec, `DB.Begin.spec`,
is proved with no `sorry` (`Proof/go_etcd_io/bbolt/DB__Begin.lean`), and it takes the caller's
`threadTok` as the read transaction's `mmaplock` reader slot. `Tx.Rollback.spec` gives the token
back. The backend still goes through the `_kv` axioms, which take no token.
`notes/bbolt-spec-decisions.md` already lists `DB.Begin_kv` (read) as "not a corollary: needs a
`threadTok` (D1)". This review shows the missing token makes the axiom false.

Go at the pins:
- bbolt is the fork `upamanyus/bbolt` `743299d8cec8` (examples' `go.mod`): `db.go:768-779` `Close`,
  `:841` `Begin`, `:866-911` `beginTx`, `:949-951` `removeTx`; `tx.go:303-378` `Rollback`,
  `nonPhysicalRollback`, `close`. These paths are as in upstream v1.5.0 (`db.go:792-877`).
- etcd is the fork `673da07c8`: `server/storage/backend/backend.go:381-423` `Snapshot`, `:481`
  `Close`, `:1129-1132` `snapshot.Close`.
- Go is go1.27.3: `src/sync/rwmutex.go:47` `rwmutexMaxReaders = 1 << 30`, `:67-80` `RLock`,
  `:114-138` `RUnlock`/`rUnlockSlow`, `:144-160` `Lock`.
- Perennial is `84d538063`.

## Verdict

| axiom | verdict |
|---|---|
| `bbolt.DB.Begin_kv.wp_proof` (with `Open_kv`, `Close_kv`, `Rollback_kv`) | **refuted**. Go fatals in 4 minutes with almost no memory, and the Lean triple is proved with no `sorry`. |
| `backend.backend.Snapshot.wp_proof` (with `snapshot.Close`, `backend.Close`) | **Stuck (Go side).** It has the same gap and the same fatal, but Go needs one live goroutine per open snapshot: 2 ^ 30 of them is about 4 TiB, against the 32 GiB cap. No smaller-count variant reaches the fatal. |

## The gap

**Go's limit.** bbolt's `beginTx` takes `db.mmaplock.RLock()` (`db.go:875`) and holds it until the
transaction ends: `Rollback` → `nonPhysicalRollback` → `close` → `removeTx`, whose first statement
is `db.mmaplock.RUnlock()` (`db.go:951`).

In `sync.RWMutex`, `RLock` increments the `int32` `readerCount` and never checks it. `Lock`
subtracts `2 ^ 30` and waits for the `r` readers it found. `RUnlock` decrements, and when the result
`r` is negative it calls `rUnlockSlow(r)`, which fatals on `r + 1 == 0` or
`r + 1 == −2 ^ 30` (`rwmutex.go:130-132`).

Step through `n = 2 ^ 30` readers and a pending writer:
1. Before the writer, `readerCount = 2 ^ 30`.
2. `Lock` brings it to `0` and blocks.
3. The next `RUnlock` brings it to `−1`, so `rUnlockSlow(−1)` runs, and `r + 1 == 0` holds.
4. `fatal error: sync: RUnlock of unlocked RWMutex`.

The bound is tight: at `2 ^ 30 − 1` nothing fires (`authrdn-count.md`'s scaled test).

**The writers on `mmaplock`** are `DB.Close` (`db.go:775`: `rwlock`, then `metalock`, then
`mmaplock.Lock`) and `mmap` (`:492`, a commit that grows the file).

**The model.** `DB.Begin_kv` with `w = false` takes `ownDB db γ D` and gives it back with a fresh
`txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx`. Nothing is consumed, so a proof can call it any number
of times.

`txLive` is an opaque axiom (`InvBbolt.lean:92`) with no tie to `mmaplock` or to Perennial's
`RWMutex` model. Perennial's model holds exactly `actualMaxReaders = 2 ^ 30 − 1` `ownRLockToken`s
per mutex (`authrdn-count.md`), and none is taken here. So the axiom hands out a reader of
`mmaplock` that no token pays for.

`Tx.Rollback_kv` needs only `txLive tx 1 ∗ rtxSnap tx D`, not `ownDB`. `DB.Close_kv` needs `ownDB`
and does not require the transactions closed. Its docstring says "it waits for the open
transactions", which a WP allows.

No thread bound is involved: one goroutine can hold all `2 ^ 30` read transactions.

## The counterexample (Begin_kv)

**Go**: `examples/axiomcx/bboltrd/bboltrd.go`, `Run(path)`:

```go
db, err := bolt.Open(path, 0600, &bolt.Options{})   // a new file
tx0, err := db.Begin(false)
for i := uint64(1); i < 1<<30; i++ { db.Begin(false) }  // never closed
go func() { db.Close() }()                           // waits on mmaplock: readerCount 2^30 -> 0
time.Sleep(time.Second)
tx0.Rollback()                                       // RUnlock: 0 -> -1, fatal
```

**The test**: `examples/axiomcx/bboltrd/bboltrd_test.go`, `TestRunFatal`. The fatal cannot be
recovered, so the test runs `Run` in a child process and checks its output. Run with
`cd examples && GOTOOLCHAIN=go1.27.3 go test -timeout 60m ./axiomcx/bboltrd/` under
`systemd-run -p MemoryMax=32G`.

- **Upstream v1.5.0** (scratch module, the same program): the 2 ^ 30 read transactions opened in
  4m8s, then
  ```
  fatal error: sync: RUnlock of unlocked RWMutex
  sync.(*RWMutex).rUnlockSlow  rwmutex.go:132
  go.etcd.io/bbolt.(*DB).removeTx  db.go:877
  go.etcd.io/bbolt.(*Tx).close  tx.go:370
  go.etcd.io/bbolt.(*Tx).Rollback  tx.go:307
  ```
  Exit status 2, 251 s wall.
- **The pinned fork** (the examples module): `TestRunFatal` passes in 263.6 s, and the child's
  output begins `fatal error: sync: RUnlock of unlocked RWMutex`.

**Memory.** It needs almost none:
- `Run` drops every `*Tx` but `tx0`, so the dropped ones are garbage.
- A database that has never had a write transaction has not loaded its freelist (`loadFreelist`
  runs only for `PreLoadFreelist` or a write transaction). So bbolt keeps no per-reader state:
  `readonlyTXIDs` stays empty, and `stats.OpenTxN` is one `int`.
- Measured at `2 ^ 22` open transactions: the live heap did not grow, 0.7 MB before and after.
  Process `Sys` was 172 MB.
- Holding the `*Tx` values would cost 312 B each (measured at `2 ^ 20`), 312 GiB for `2 ^ 30`. A
  loaded freelist would add 8 B per reader, 8 GiB.

It fires every time, given the one-second sleep: the `Rollback` must come after `Close` is
pending. Without the sleep, a `Rollback` that comes first leaves `2 ^ 30 − 1` readers, and `Close`
then blocks for good, which is a deadlock, not a counterexample.

**Translation**: a temporary goose project, `axiomcx-bboltrd` in `etc/goose.py`, on this branch
only. It produces `Code/github_com/mit_pdos/etcd_grove/examples/axiomcx/bboltrd.lean` and
`GeneratedProof/.../axiomcx/bboltrd.lean`.

**Proof**: `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/bboltrd/Run.lean`.
- `Run.wp_proof` proves `{{ isPkgInit bboltrd ∗ fileHolds path ∅ }} Run #path {{ RET #(); True }}`
  from the four specs it calls (`Open_kv`, `DB.Begin_kv`, `DB.Close_kv`, `Tx.Rollback_kv`), taken as
  hypotheses, and Perennial's proved `time.Sleep`.
- The loop's invariant is `i ↦ j ∗ ownDB db γ ∅`. Each iteration's `txLive`/`rtxSnap`/`rtxStats` is
  dropped.
- `wp_fork` hands `ownDB` and `dbFile` to the `Close` goroutine. Its post is `True`, since
  `Close_kv` returns.
- `tx0`'s `txLive tx0 1 ∗ rtxSnap tx0 ∅` pays for `Rollback_kv`.
- `Run.wp_axioms` instantiates the four hypotheses with the axioms.

`lake build` of the module succeeds with no `sorry`. `#print axioms Run.wp_axioms` shows:
- Lean's three;
- the four `*.wp_proof` axioms;
- bbolt's predicate model (`ownDB`, `wrTok`, `isDB`, `isDB_persistent`, `txLive`, `txDB`, `txDone`,
  `rtxSnap`, `rtxSnap_persistent`, `rtxStats`, `ownWTxG`, `fileHolds`, `dbFile`, `boltLogger`);
- the `Options` rules (`optsAt`, `optsVal`, `wp_optsLit`, `wp_optsAlloc`);
- the type declarations of untranslated Go types (`runtime.*`, `os.*`, `reflect.*`, `unix.Itimer*`,
  ...), which carry no behaviour.

That is the same set, in kind, as `bboltnan`'s `Run.wp_axioms` (`bbolt.md`). Nothing else, and no
`sorryAx`. The proof also takes the generated `Assumptions` classes of bbolt, `time` and the
counterexample package, as every proof here does.

## Snapshot: the same gap, Stuck in Go

**The model program.** It uses a backend constructed and opened as in `backend.New`'s post. With
`R := emp` and `Q := fun _ _ _ _ => True`, the observation wand is trivial.
1. Call `b.Snapshot()` `2 ^ 30` times. Each call consumes one `wbTok`, of `2 ^ 40 − 1`. Each returns
   `bOpen γ qo` and a fresh `snapOpen sp D`.
2. Fork `b.Close()`. Its premise `bOpen γ 1` is whole again, since every `Snapshot` returned its
   share.
3. Call `snapshot.Close` on one snapshot. It needs only `snapOpenQ sp D γ 1`.

The specs say every call returns.

In Go, `backend.Close` stops `run`, takes `b.mu.Lock()` and calls `b.db.Close()`. That is a
pending `mmaplock` writer behind the snapshots' `2 ^ 30` readers. `snapshot.Close` then calls
`tx.Rollback()` (`backend.go:1132`), which reaches the same `removeTx` fatal.

Neither `Snapshot` nor `snapshot.Close` mentions `mmaplock`, a `threadTok` or a count. The axiom
also forks the warning goroutine (`backend.go:393`) without a thread token: the spec lets a
standalone triple hold `2 ^ 30` such goroutines at any thread bound.

**Why Go cannot run it under the cap.** `Snapshot` always starts a goroutine, which lives until
`snapshot.Close` (`<-s.donec`). So `2 ^ 30` open snapshots are `2 ^ 30` live goroutines.

Measured with etcd's backend at the pin (`backend.New(DefaultBackendConfig)`, `2 ^ 16` open
snapshots, then `runtime.GC`):

| per open snapshot | bytes |
|---|---|
| heap (the `*Tx`, `snapshot`, two channels, ticker, goroutine closure, `readonlyTXIDs` slot) | 1551 |
| goroutine stacks (`StackInuse`) | 2322 |
| total `Sys` growth | 4303 |

For `2 ^ 30` open snapshots that is `2 ^ 30 × 3873 B ≈ 3.8 TiB` live (`Sys` growth: 4.2 TiB). The
cap allows `32 GiB / 4303 B ≈ 8.0 × 10 ^ 6 ≈ 2 ^ 23` open snapshots, a factor of `2 ^ 7` short.

**No smaller-count variant.** `RWMutex` misfires only when the count of outstanding readers
reaches `2 ^ 30`:
- `rUnlockSlow`'s fatal needs `readerCount ∈ {−1, −2 ^ 30 − 1}` after a decrement. With `n`
  readers outstanding, no writer and a well-paired `RUnlock`, the count after it is `n − 1 ≥ 0`.
  With a writer, it is `n − 1 − 2 ^ 30`, which equals `−1` only at `n = 2 ^ 30`.
- `Unlock`'s fatal ("Unlock of unlocked RWMutex", `rwmutex.go:209-212`) needs `2 ^ 30` readers to
  arrive while the writer holds it. Each one is a blocked goroutine.
- The writer's subtraction cannot be applied twice: `Lock` first takes `rw.w`.
- The backend's other `mmaplock` readers are no cheaper. They are the current `readTx.tx` (one)
  and the rotated ones, each waiting in its own rollback goroutine (`batch_tx.go`'s
  `unsafeCommit`). A program cannot reach the backend's `*bolt.DB`, since `ownDB` is inside the
  batch lock's invariant.

So every Go route to the fatal through `Snapshot` takes `2 ^ 30` goroutines. No Lean proof was
built for `Snapshot`, because without a Go run the program would demonstrate nothing beyond the
`Begin_kv` counterexample. The proof would be routine (the program above: four specs, a loop, a
fork).

**What it means for the closed results.** No closed result is shown false. Through `NewServer`,
every read transaction and snapshot the verified code opens is tied to a live goroutine or is the
one current `readTx.tx` (`authrdn-count.md`, attack 8). The bounded semantics' `T ≤ 2 ^ 28` keeps
these below `2 ^ 30`. But that argument lives outside the logic.

`Begin_kv` itself is used only by the verified backend (`backend__begin`, `unsafeCommit`,
`newBackend`), never by a program on its own `*bolt.DB`. The `tcb-report.py` run below lists 99
roots that reach `bbolt.DB.Begin_kv.wp_proof` and 69 that reach `backend.backend.Snapshot.wp_proof`.
Among them are every closed result through the server:
- `etcd_putget_safe`, `etcd_putget3_safe`, `etcd_watch_safe`;
- `etcd_lease_safe`, `etcd_leasegrant_safe`, `etcd_leaseexpiry_safe`, `etcd_leasecatchup_safe`;
- `etcd_compacted_safe`, `etcd_compactwatch_safe`, `etcd_cache_safe`, `etcd_txnlin_safe`;
- `etcd_partition_safe`, `etcd_partition_watch_safe`;
- `k8s_compactor_safe`, `k8s_compactor_partition_safe`, `k8s_etcd3_safe`;
- `authkv_Main`;
- and `Begin_kv`'s also reach the mvcc results `mvcc_NewStore_backend*` and `mvcc_backend_bridge`.

That run was `LAKE_OPTS=--packages=... etc/tcb-report.py --reuse --roots
'^Spec/go_etcd_io/etcd/server/v3/storage/backend/' 'bbolt'`, then `.lake/tcb.json` grepped for
every root.

These results rest on a false axiom. Their statements stay true of Go only by the goroutine
argument above, which no proof checks.

## Attacks tried

1. **2 ^ 30 read transactions from one goroutine, then `Close` and a `Rollback`** (`Begin_kv`):
   refuted, as above.
2. **The same through a remap instead of `Close`** (a `Commit` that grows the file past the
   mapping, `db.go:492`): the same fatal in Go. In the model it needs `ownDB` and `wrTok` in the
   writer, which are free while the readers hold only `txLive`. Not built: `Close` is simpler.
3. **2 ^ 30 snapshots, then `backend.Close` and `snapshot.Close`**: the model allows it, Go fatals
   by the same path. Stuck: about 4 TiB of goroutines.
4. **A smaller count** (the writer side's subtraction, `Unlock`'s fatal, nested readers): none
   reaches a fatal below `2 ^ 30` outstanding readers (above).
5. **`RLock` itself past `2 ^ 30`**: no check. At `2 ^ 31` the `int32` wraps negative and `RLock`
   blocks, which is a hang, not a fatal.
6. **Perennial's model.** In the proved bbolt, the reader slot is a verified `ownRLockToken` from a
   pool lent for the caller's `threadTok` (`Spec/go_etcd_io/bbolt/Api.lean:80-104`;
   `Open` takes `ThreadBoundLe GF (2^29)`). That accounting cannot exceed `2 ^ 30 − 1` readers. The
   `_kv` axioms bypass it: `ownDB`/`txLive` are opaque, and `Begin_kv`'s post is not derived from
   `DB.Begin.spec`.

**Not tried:** the closed adequacy form of the counterexample; a Lean proof of the `Snapshot`
program; 32-bit platforms.

## Proposed true restatement (not applied)

This is `notes/bbolt-spec-decisions.md`'s D1, carried to the `_kv` layer and to `Snapshot`.

- **`DB.Begin_kv`, read mode**: take `threadTok` when `w = false`. Its error branch gives the token
  back. Its success branch keeps it inside the transaction: `txLive tx 1` holds the slot, or a
  separate `rtxSlot tx` does.
- **`Tx.Rollback_kv`**: return the `threadTok` (`txDone tx ∗ threadTok`).
- **Better still**: retire the read half of `Begin_kv` for the proved `DB.Begin.spec`, as the D7/D1
  plan intends.
- **`backend.Snapshot`**: take a `threadTok` held by the snapshot until `snapshot.Close` returns it
  (`snapOpen` holds it). It needs a second token for the warning goroutine, unless the one token
  is read as paying for both. That works because the goroutine and the read transaction live and
  die together (`snapshot.Close` waits on `donec`, then rolls back), so one token per open
  snapshot bounds both.
- **The backend's callers**: `notes/bbolt-spec-decisions.md`'s "the thread-token flow" lists them
  (`New` takes and returns a token; `unsafeCommit`'s rollback fork pays for the new `begin(false)`).
  The snapshot path's caller (`etcdserver`'s `snapshot` send) would pay from the goroutine that
  sends it.

Any of these changes trusted statements and their clients' proofs: the user's decision.
