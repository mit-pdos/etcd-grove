# `lease.NewLessor.wp_proof` (`lessorApplyOk` at `T := wbTok`, `R := bkRT ∗ RW`): survives

**Reviewed** 2026-11-06, at `mvcc-api` `b4bc6a538c` (the change: `1b56c352f8`; etcd fork
`ce3dbc097f`; go1.27.3), by the `axiom` skill. No branch (no commit, no `lake`, as asked).

## The axiom and the change

`lease.NewLessor.wp_proof` (`Proof/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`), its triple in
`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`. Its conclusion includes `lessorApplyOk lp`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean:134`):

```lean
□ ∀ (d : mvcc.KBReal) W Pk (f : GoFunc) RW,
  backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
  rwLens RW (lease.lessorBeOn lp d.be) -∗
  lease.lessorBackend lp Pk #f (backend.wbTok d.γB) iprop(apply.bkRT d ∗ RW)
    (backend.rbPart d.γB (· = "lease"))
```

`lessorBackend lp P f T R Rb` (`Proof/.../lease/LessorBackend.lean:102`) is `∃ b, leaseBackend b P f
T R Rb ∗ □ (R -∗ ∃ dq, le.b ↦{dq} b ∗ (le.b ↦{dq} b -∗ R))`; `leaseBackend`/`leaseBatchTx`
(`:57-90`): `BatchTx()` returns a `tx` with an abstract lock token `Lk`;
`{{ csContractA P g Pre Q Post ∗ T ∗ R }} tx.LockInsideApply() {{ Lk (Post ∗ R) }}` (for `f = #g`),
`{{ ⌜|k| = 8⌝ ∗ Lk R' ∗ schema.Lease ↦□ bk ∗ k, v ↦*□ ∗ Rb r }} tx.UnsafePut(bk, k, v) {{ Lk R' ∗ Rb
(rbSet r "lease" k v) }}`, `{{ Lk R' }} tx.Unlock() {{ R' }}`.

`1b56c352f8` moved the lens of `le.b` from the write token `T` to the lent resource `R`, and the
write right `RW` with it: before, `T := wbTok d.γB ∗ RW` (consumed by `LockInsideApply`, so a write
lost the caller's half of `le.b`) and `R := mvcc.bkRTx d.γB d.P d.be`; now `T := wbTok d.γB` and `R
:= bkRT d ∗ RW` (given back by `Unlock`). `apply.bkRT d` is `rdTok d.γB d.P d.be ∗ bOpen d.γB
rdOpen`, the old `bkRTx` exactly. `lessorBeOn lp be` is `le.b ↦{½} ok(*backend, be)`; the lessor's
lock holds the other half (`lessorExtra`); `rwLens RW X := □ (RW -∗ X ∗ (X -∗ RW))`.

## Verdict: survives

The change gives the client back what Go never takes away: a write (`persistTo`) reads `le.b`
and never writes it, so the caller's half of `le.b` is unchanged by a `Grant` or a `Checkpoint`.
No counterexample.

## The Go code

`server/lease/lease.go:55-61`: `persistTo(b)` is `tx := b.BatchTx(); tx.LockInsideApply(); defer
tx.Unlock(); schema.MustUnsafePutLease(tx, &lpb)` (one `tx`, so one `Lk` in the model);
`MustUnsafePutLease` (`storage/schema/lease.go:48-56`) marshals (a `leasepb.Lease` of three
integers: no error) and `UnsafePut(Lease, leaseIDToBytes(id), val)`, an 8-byte key.
`lessor.Grant` (`lessor.go:281-324`) and `Checkpoint` (`:367-383`) call `l.persistTo(le.b)` under
`le.mu`; `Recover` (`:600-609`) writes `le.b` under `le.mu` and calls `initAndRecover`, which creates
the `Lease` bucket (`:808-835`); `newLessor` sets `le.b` before `initAndRecover`. No other write of
`le.b`. The backend (`storage/backend/batch_tx.go`): `LockInsideApply` locks and runs the post-lock
hook; `unsafePut` (`:169-190`) `lg.Fatal`s on a missing bucket (an exit; `zap.Logger.Fatal.spec`'s
post is `False`); `Unlock` writes the buffer back (one `wbTok`) and may commit at the batch limit.

## Attacks tried

1. **A write without the batch lock.** `UnsafePut`'s and `Unlock`'s triples need `Lk _`, which only
   `LockInsideApply`'s post produces (`Lk` is existential in `leaseBatchTx`, chosen by the axiom).
   `Unlock` consumes it; no triple duplicates it. Two `BatchTx()` calls give two existentials, each
   usable only through its own `LockInsideApply`; a second `LockInsideApply` while the first is held
   deadlocks in Go (not a counterexample). Blocked.
2. **Duplicate backend access through the returned `RW`.** `R` goes into `Lk (Post ∗ R)` for the
   critical section and comes back at `Unlock`: the client never holds `RW` while the lock is
   held, so it cannot start a second lessor write (whose `LockInsideApply` needs `R`) inside the
   first. Concurrent writers from two threads each need an `RW` lending `lessorBeOn lp d.be`, an
   exclusive half; and Go serializes them anyway (`le.mu`, the batch lock). The persistent
   `lessorApplyOk` itself grants nothing without `wbTok` (one per write, consumed), `bkRT d` and
   `RW`. Blocked.
3. **Writing to a backend the lessor is not on** (a closed one after a snapshot install, `Recover`).
   `rwLens RW (lessorBeOn lp d.be)` ties `d.be` to `le.b`'s current value; after `Recover` the only
   half of `le.b` names the new backend, so the old `d` has no `RW`. `bkRT d` carries a share of
   `bOpen d.γB`, so the backend is open (after `Close`, `commit(true)` leaves the batch transaction
   without a bolt transaction, and a put would dereference it). Blocked.
4. **The lens as a source of extra ownership.** The lens takes `R` (so `RW`) and returns an
   unknown fraction `dq` of `le.b` with the wand back to `R`. A client can combine that fraction only
   with fractions it owns; the lock's half is inside the lessor's invariant. The true model has
   `dq = ½` through `RW`'s `lessorBeOn`, so no `dq` leads to `False`. `b` must be `ok(*backend,
   d.be)` by agreement with `lessorBeOn`, so `leaseBackend b` is about `d`. Blocked.
5. **The put into a missing `Lease` bucket.** `Rb r = rbPart d.γB (· = "lease") r` accepts any `r`,
   including one without `lease`, and claims the put returns. In Go, `le.b` is only ever a backend
   on which `initAndRecover` created the bucket (attack 3's tie); deleting it later takes the client
   half of the tracked bucket and the batch lock (`UnsafeDeleteBucket.spec`), after which Go's put
   `lg.Fatal`s: `os.Exit(1)`, not a panic (`zap.Logger.Fatal`'s post `False` models it as divergence;
   the skill's rules exclude exits). Not a counterexample; noted for the audit row.
6. **The hook.** `LockInsideApply` runs `f` under the lock's invariant `Pk` (`csContractA Pk g …`,
   `hookRun` at `f ≠ nil`: `□ {{ Pk ∗ Pre }} f() {{ Q }}`), and `plHookRO d.γB f` freezes the
   backend's hook at `f`. Unchanged by the commit; the same shape as before strict M1 (`mvcc.csContract`).
7. **Write-back count.** `T = wbTok d.γB` is spent at `LockInsideApply` for the one write-back of
   `Unlock` (`pending != 0`); the post of a `Grant` that fails before `persistTo` gives no token back,
   which only charges more than Go spends. Blocked.

## Side finding (outside the target)

`zap.Logger.Fatal.spec` and the other `zap.Logger` method axioms (`Info`, `Debug`, `Warn`, `Error`,
`Panic`, `Spec/go_uber_org/zap/`) take only `⌜l ≠ null⌝`. A zero `zap.Logger` (`&zap.Logger{}`, legal
Go: the struct is translated, `Code/go_uber_org/zap.lean:1383`) panics with a nil dereference in
`Fatal` and in `Info` (go1.27.3, the examples module's zap; a throwaway test, deleted:
`recovered: runtime error: invalid memory address or nil pointer dereference`). So `Info`'s triple
(post `RET #()`) and `Fatal`'s (post `False`, which a panic violates) are false of a zero logger.
Not reviewed further (no Lean proof): a premise that `l` was made by a zap constructor
(`zap.NewNop`, `Config.Build`) would repair them. `notes/audit.md`'s zap rows say "ok".
