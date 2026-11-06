# `authSchemaSrv`'s count: `backend.authRdN = 2 ^ 28 + 2 ^ 7`

**Reviewed (2026-11-06, branch `revoke-open` at `c4c73affdc`; this report on `axiom/authrdn-count`):**
the trusted premise `authSchemaSrv` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthSrv.lean:81`, the
named premise `hD22` of `srv_auth_tp_on`, `server_new_auth_on`, `authkv_startServer`, `authkv_Main`),
whose text is unchanged but whose count changed (revoke-open Q6 (a), §H of
`notes/revoke-open-plan.md`):

```lean
-- Proof/go_etcd_io/etcd/server/v3/storage/backend/RdPool.lean, lean -> revoke-open
@[word_unfold] def authRdN : Nat := 2 ^ 7              -- old
@[word_unfold] def authRdN : Nat := 2 ^ 28 + 2 ^ 7     -- new
theorem rdStockN_val : rdStockN = 805306239            -- old
theorem rdStockN_val : rdStockN = 536870783            -- new
```

The premise takes `authRdSlots d` (`backend.rdAuth`: `authRdN` copies of `rdTok`, the backend's reader
slots) and gives `authRdN` copies of the store's reader resource `R` (tickets). The question (the
coordinator's condition): does the backend's `readTx` reader partition stay below `2 ^ 30 − 1`, against
the pinned code, and can a program with that many readers make Go panic while the premise says it
does not?

Go at the pins: etcd `upamanyus/etcd` `673da07c8` (`server/storage/backend/{backend,read_tx,batch_tx}.go`,
`server/storage/schema/{auth,schema}.go`, `server/auth/store.go`, `server/etcdserver/server.go`), bbolt
v1.5.0 (`db.go`), go1.27.3 `src/sync/rwmutex.go`; Perennial `84d538063` (`Proof/sync/RWMutexDefs.lean`,
`RWMutexGuard.lean`, `GooseLang/{Threads,BoundedLang}.lean`).

**Verdict: survives.** The partition is exactly `2 ^ 30 − 1`, each of its slots is one verified RLock
token of `readTx.mu` and of `txMu`, the premise trades slots for tickets one for one, and the auth store's
Go code takes one `readTx.mu` read lock per ticket in use. Go's limit is tight at `2 ^ 30 − 1` (a scaled
copy of the RWMutex shows it), and it is never approached. Two side findings (attacks 6 and 8) concern
other axioms, not this count.

## The partition arithmetic

| holder | count | value |
|---|---|---|
| the backend's pool (`rdPoolN`, a `threadPool` of `rdTok`) | `2 ^ 28` | 268435456 |
| the auth store's share (`authRdN`, `rdAuth`) | `2 ^ 28 + 2 ^ 7` | 268435584 |
| the counted stock (`rdStockN`) | `2 ^ 30 − 1 − 2 ^ 28 − (2 ^ 28 + 2 ^ 7)` | 536870783 |
| **total** = the constructor's `actualMaxReaders` | `2 ^ 30 − 1` | 1073741823 |

`rdStockN` is defined as the `Nat` difference `actualMaxReaders − rdPoolN − authRdN`, and
`rdPoolN_add_rdStockN : rdPoolN + authRdN + rdStockN = actualMaxReaders` is proved by `decide` (so the
subtraction does not truncate: `2 ^ 28 + 2 ^ 28 + 2 ^ 7 ≤ 2 ^ 30 − 1`); `rdStockN_val` is `decide` too.
`rdToks_pool` splits the constructor's `actualMaxReaders` `rdTok`s into exactly these three; nothing else
takes `rdTok`s from `newPost`/`newPostK`.

Downstream of the auth share (not part of the backend partition, but the reason for the raise):
`authRdSupply` hands the server `authRdN − 1 = 2 ^ 28 + 127` tickets; `NewServer` takes 1 + 1 + 64 + 1 = 67
(`NewServer.lean:931-937`), leaving `2 ^ 28 + 60 ≥ 2 ^ 28 − 1` for the revocation's inner pool `I`; the
`authRdN`-th is the auth applier's (`Recover`).

## Go's limit

`sync.RWMutex` (go1.27.3 `rwmutex.go:47-212`): `rwmutexMaxReaders = 1 << 30`; `readerCount` is an
`int32` that every `RLock` increments **before** blocking (a reader waiting behind a writer counts);
`Lock` subtracts `2 ^ 30`. With `n` counted readers and a writer pending, `readerCount = n − 2 ^ 30`. If
`n ≤ 2 ^ 30 − 1` it stays negative, new readers block, and `rUnlockSlow`'s check
`r+1 == 0 || r+1 == -rwmutexMaxReaders` never fires. If `n ≥ 2 ^ 30`, the count reaches `0` after `Lock`
(a new reader enters beside the pending writer) and the reader that takes it from `0` to `−1` hits
`fatal("sync: RUnlock of unlocked RWMutex")`. `RLock` itself never checks the count. So **Go admits up to
`2 ^ 30 − 1` counted readers, and that bound is tight.**

Scaled check (`/shared/tmp/authrdn-scaled`, deleted afterwards): go1.27.3's `RWMutex` copied with
`rwmutexMaxReaders = M = 8`, the semaphores replaced by channels and `fatal` by `panic` (the counter
arithmetic unchanged). `n` readers hold, a writer arrives, the readers leave:

```
readers=1..7 (M=8): ""                                    (the writer gets the lock)
readers=8   (M=8): "sync: RUnlock of unlocked RWMutex"
readers=9   (M=8): "sync: RUnlock of unlocked RWMutex"
readers=10  (M=8): "sync: RUnlock of unlocked RWMutex"
holding=4 arriving=3 total=7 (M=8): ""                    (blocked readers count)
holding=4 arriving=4 total=8 (M=8): "sync: RUnlock of unlocked RWMutex"
holding=1 arriving=6 total=7 (M=8): ""
holding=1 arriving=7 total=8 (M=8): "sync: RUnlock of unlocked RWMutex"
```

Perennial's `RWMutex` proofs are over Goose's translation of this code (`Code/sync.lean`: `RLock`,
`RUnlock`, `rUnlockSlow` with the fatal, `Lock`); the invariant holds `ownToks rlockOverflowGn
pos_reader_count` under `ownTokAuth … actualMaxReaders` (`RWMutexDefs.lean:122-126`), and
`init_RWMutex` makes exactly `actualMaxReaders = 2 ^ 30 − 1` `ownRLockToken`s (`:716-731`). The
guarded `sync.ownRWMutex` that `rdTok` holds of `readTx.mu` and of `txMu` (`InvBackend.lean:1293-1302`)
is one such token each (`RWMutexGuard.lean:125-127`). So the logic can never have more than `2 ^ 30 − 1`
readers of either mutex counted, whatever the partition: a forged count would need a forged token.

## Attacks tried

1. **The arithmetic.** Checked by hand and by the two `decide`s: the three parts sum to
   `2 ^ 30 − 1` exactly; `Nat` subtraction does not truncate. The `decide`s at `AuthSrv.lean:324,461`
   (`authRdN − 1 ≤ actualMaxReaders`) hold. No double count: `bkRPool` carries the open shares of
   `rdPoolN + authRdN` slots (`bOpen_one_pool`), the stock the other `rdStockN`, `bOpen γ 1` in all.
2. **More tickets than slots.** The premise is persistent (`□ ∀ …`), so a proof can call it again. Each
   call consumes `authRdSlots d` (`authRdN` `rdTok`s) and returns `authRdN` tickets of a fresh `R`; a
   second call on the same backend must find `authRdN` more `rdTok`s (the stock has 536870783 ≥
   268435584, so it can), and they are consumed too. Every ticket ever issued is backed by a slot
   consumed for it; the snapshot clause (`authSchemaSnap`, also `□`) likewise takes the new backend's
   `authRdSlots`. No call creates readers out of nothing.
3. **One ticket, two read locks (nesting).** If Go took two `readTx.mu` read locks per ticket in use,
   `authRdN` tickets could stand for `2 · authRdN` readers (`2 ^ 29 + 2 ^ 8`), past the partition. Go:
   `authReadTx.RLock` is `be.ReadTx().RLock()` (`schema/auth.go:146-152`, the shared `readTx.mu`, not a
   `ConcurrentReadTx`); the auth store takes it in `lockedReadTx` (`store.go:941-948`: `beMu.RLock`,
   `ReadTx().RLock()`, `beMu.RUnlock`, the read lock returned) and `Recover` (`:403-410`); every
   caller (`CheckPassword` `:374`, `isOpPermitted` `:882`, `IsAdminPermitted` `:923`) releases it with
   a `defer` and calls nothing that takes another (`UnsafeGetUser`, `hasRootRole`,
   `isRangeOpPermitted` read the open transaction or the permission cache). Inside, `UnsafeRange`
   takes `txMu.RLock`/`Lock` briefly (`read_tx.go:96-120`), covered by `rdTok`'s `txMu` slot. One lock
   per ticket.
4. **Tickets across backends.** A ticket is redeemed against the backend current at `lockedReadTx`,
   and the old backend's `authRdN` slots stay with the realization for good. A reader still on the old
   backend holds one of the old slots; the new backend's readers hold at most the remaining tickets.
   Per backend, auth readers ≤ `authRdN`. Each backend has its own `readTx.mu` and `txMu`
   (`backend.go:255-256`; `reset` renews only `txWg`, `concurrentReadTx` shares the pointer `txMu`).
5. **`txWg` and the budget token.** `rdTok`'s `crTok` carries one `γ.rdt` token, the budget for
   `ConcurrentReadTx`'s `txWg.Add(1)` (`backend.go:301-305`). The `WaitGroup` counter is the high
   `int32` of its state (panics only when negative, or on misuse with `Wait`): `2 ^ 30 − 1 < 2 ^ 31`.
6. **Readers of `readTx.mu` outside the partition.** The verified backend code takes `readTx.mu` read
   locks only with a caller's `rdTok` (`ConcurrentReadTx`, `reader_RLock`); its own `readTx.Lock`s
   (`batch_tx.go:330,376`, defrag `backend.go:643,753`) are writers. Among the axioms: the membership
   reader (`MustReadMembersFromBackend`) takes `bkRPool` and a `threadTok` (a pool slot); `SetBackend`
   and the lessor's specs use the batch transaction; `VerifyBackendConsistency` read-locks `readTx.mu`
   with nothing in its precondition, but only under `ETCD_VERIFY` (`verify.go:73-91`; the audit's
   deployment assumption). **One reader is not counted:** `EtcdServer.monitorStorageVersion`'s goroutine
   calls `StorageVersion` (`server.go:2227-2232`) → `schema.DetectSchemaVersion` (`schema.go:85-88`),
   which takes `readTx.RLock()`, while its spec (`srvSVRes`: a reader slot of `s.bemu` and of `lg`)
   holds no `rdTok`. So Go's `readTx.mu` can have one reader more than the logic counts. It cannot
   reach Go's limit: every `readTx.mu` reader in etcd's code is a goroutine inside a critical section
   (holding at most one: attack 3, and no code keeps a locked transaction past its goroutine), live
   goroutines are at most the bounded semantics' `T` (`BoundedLang.lean`: a `Fork` without thread fuel
   stutters; the adequacy theorems cover executions with at most `T` live threads), and every closed
   theorem through `NewServer` has `T ≤ 2 ^ 28` (J8a-6). So Go's readers are at most `2 ^ 28`, far
   below `2 ^ 30 − 1`. Not a counterexample to the count; a precision note for the partition's
   docstrings, which say "the backend's `readTx` reader partition" as if it counted every Go reader.
7. **The count at the closed level.** The raise moves `2 ^ 28` slots from the stock to the auth share;
   no consumer of the stock needs more than what is left (`mvcc.nReaders_val`, `InvStore.lean:5040`, is
   restated at 536870783 on the branch, and its users `SnapApplyWalk.lean:765`, `StopShutdown.lean:584`
   rewrite with it; green per `c4c73affdc`). The raise
   does not change what Go does; it only lets the logic hand out `2 ^ 28` more tickets, each backed by a
   slot.
8. **bbolt's `mmaplock` (the coordinator's "bbolt's tx/db").** Not part of this partition, but the same
   shape: every bbolt read transaction holds `db.mmaplock.RLock()` until its rollback (`db.go:792-812,
   875-877`), and `mmap` (a commit that grows the file) and `Close` take its write lock (`:456-458`,
   `:701-702`). The backend's own read transactions are its current `readTx.tx`, the rotated ones
   waiting in their rollback goroutines (`batch_tx.go:388-404`), and `Snapshot`'s (`backend.go:381-423`,
   one per open snapshot, each with a goroutine until `Close`). Under the thread bound these are at most
   `T + 1` live, below `2 ^ 30` when `T ≤ 2 ^ 28`, as in every closed theorem through `NewServer`.
   **Lead (not pursued, another axiom):** `backend.backend.Snapshot.wp_proof` and `bbolt.DB.Begin_kv`
   bound neither the open snapshots nor the read transactions (`Snapshot` consumes a `wbTok`, of which
   there are `wbInit = 2 ^ 40 − 1`), and no backend spec needs a thread bound. A standalone program
   (no `NewServer`) proved at an adequacy `T > 2 ^ 30` could open `2 ^ 30` snapshots, close the backend
   or grow the file from another goroutine (a pending `mmaplock` writer), and close a snapshot: Go
   fatals with "sync: RUnlock of unlocked RWMutex". Needs `2 ^ 30` goroutines in Go (terabytes of
   stacks), the same idealization as every bound here. Worth a separate `axiom` run on
   `backend.Snapshot`/`Begin_kv` if the backend's standalone triples matter.

## What was not tried

- No Lean counterexample (none is due: the count survives). No `lake build` on this branch: the review
  reads the statements and the `decide`d arithmetic at `c4c73affdc`, which its commit reports green.
- The auth store's own `beMu` reader count (`lockedReadTx`'s `beMu.RLock`) is the store's proved
  accounting, not this premise's.
- The pass-2 consumers of the raised supply (`I`'s `2 ^ 28 − 1` items, `srvRevokePoolN`) are DRAFT
  `sorry`s on the branch; their arithmetic was checked only against `authRdSupply`'s count above.

## Results resting on the premise

As a named premise (`hD22 : ⊢ authSchemaSrv`), not an axiom: `srv_auth_tp_on`, `server_new_auth_on`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/Results.lean:2035,2079`), `authkv_startServer`,
`authkv_Main` (`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/Results.lean:66,79`).
