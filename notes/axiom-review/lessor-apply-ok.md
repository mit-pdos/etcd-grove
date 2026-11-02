# `lessorApplyOk`: the lessor's backend contract (axiom review, 2026-11-02)

**Reviewed**: `lessorApplyOk lp` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean:123`), the
conjunct of `lease.NewLessor.spec`'s post (`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`, the
axiom `lease.NewLessor.wp_proof`) that the apply thread's grants and checkpoints rest on, through
`lease.lessorBackend`/`leaseBackend`/`leaseBatchTx` (`Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean`),
at branch `lease-grant` `7d62260a7c`. Two texts:

- **current**: `lessorBackend lp Pk #f (wbTok d.γB ∗ RW) (bkRTx …) (rbPart d.γB (· = lease))`,
  for every real backend `d`, `W`, `Pk`, frozen non-nil hook `f` and write right `RW` with
  `rwLens RW (lessorBeOn lp d.be)`: `RW` is spent with the write-back token at `LockInsideApply`;
- **proposed** (`notes/lease-grant-plan.md`, "Design of the server chain", 2.12 and the freeze
  list): `lessorBackend lp Pk #f (wbTok d.γB) RW (bkRTx …) (rbPart …)`, with a new argument `Ln`
  (the lent part) whose lens `□ (Ln -∗ ∃ dq, lF "b" lp ↦{dq} b ∗ (… -∗ Ln))` replaces `T`'s;
  `Grant.spec`/`Checkpoint.spec` take `T ∗ Ln ∗ R ∗ Rb rb` and give `R ∗ Ln` back in every arm (`T`
  spent in both). Stated here as written in the plan; not in code.

Read with them: `lease.lessor.Grant.spec`, `Checkpoint.spec`, `Revoke.spec`, `Recover.spec`,
`Lease.persistTo.spec`; the real backend's `batchTxBuffered.{LockInsideApply,UnsafePut,Unlock}.spec`,
`backend.New.spec`, `ConcurrentReadTx.spec`; Go at the etcd pin (`/shared/etcd-goose-lean-wk`,
`server/lease/{lessor,lease}.go`, `server/storage/schema/lease.go`,
`server/storage/backend/{batch_tx,backend,verify}.go`).

## Verdict

**Both texts survive** every attack tried. No Go program found that panics, or returns a wrong
result a later check would catch, under a proof from either text. Neither text gives out a resource
it did not take: every `LockInsideApply` takes one `wbTok` and the open share `R` and its `Lk` token
is the only way to `Unlock`, which gives back `Post ∗ R` and nothing else; the proposed `Ln` is
only read through and returned whole.

## The claims

1. `b.BatchTx()` returns a transaction (`persistTo`'s `b` is the value `Grant`/`Checkpoint` read from
   `le.b` under `le.mu`, `lessor.go:312,375`; the lens pins it to `d.be`).
2. `LockInsideApply()` under `csContract Pk f Pre Q Post`, with `wbTok ∗ (RW)` and `bkRTx`, gives
   `Lk (Post ∗ R)` (the axiom runs the hook and the caller's update).
3. `UnsafePut(Lease, k, v)` with `|k| = 8`, `↦*□` slices and the lease bucket's part at `r` keeps
   `Lk` and gives the part at `rbSet r "lease" k v`.
4. `Unlock()` turns `Lk X` into `X`.
5. (proposed) `Ln` lends the field and is not needed by 2–4.

## Attacks tried

| # | attack | result |
|---|---|---|
| 1 | **Counted: write-back tokens.** Does any path `Unlock` twice per token, or write back without one? | `persistTo` (`lease.go:55-61`) is one lock, one put, one deferred `Unlock`; `Grant`/`Checkpoint` call it at most once (`lessor.go:312,375`). Go check `TestOneLockPerWrite`: 2000 grants run the post-lock hook exactly 2000 times, 2000 persisting checkpoints 2000 more; rejected grants and a checkpoint of an absent lease none. The specs spend `T` on those paths too (weaker, sound). |
| 2 | **Counted: the batch lock.** Forge or reuse `Lk`: a second `Unlock`, `Lk` of one `BatchTx()` result or one instantiation used with another, an `Unlock` from inside the hook `f` (Go would then hit `sync: unlock of unlocked mutex` at the real `Unlock`). | `Lk` is existential per `leaseBatchTx` fact and produced only by `LockInsideApply`; `f` runs before it exists, and the real backend's `batchLocked` (which the backend's own `Unlock.spec` needs) is never handed out by the axiom. A second `LockInsideApply` while one is held needs a second `wbTok`/`R` (and, current text, a second `lessorBeOn`, impossible) and in Go blocks (`batchTx.lock`, `batch_tx.go:107`): a deadlock, no panic. |
| 3 | **Counted: the open share `R = bkRTx`.** Close the backend between lock and unlock (Go: `UnsafePut` on a stopped transaction). | `R` is inside `Lk` until `Unlock`; `Close` needs every share of `bOpen`. Returned unchanged; `LockInsideApply` needs only `bOpen`'s share, `rdTok` is idle. |
| 4 | **Counted: the lent part `RW`/`Ln` (Q4).** Current: `RW` is consumed at `LockInsideApply` and never returned (true, but the apply thread can grant once: the plan's motivation). Proposed: is anything given back that the call did not take, or does returning `Ln` let `Recover` move `le.b` while a write is in flight? | `Grant`/`Checkpoint` read `le.b` once, under `le.mu`, and hold `le.mu` to the end (`defer`), `persistTo`/`LockInsideApply`/`Unlock` never write the field; `Recover` writes it only under `le.mu` (`lessor.go:600-609`) with both halves (its spec takes `lessorBeOn`). `Ln` is held across each spec, returned at the end: no window. |
| 5 | **The tracked part `Rb`.** The put takes `rbPart (· = lease) r` for any `r` and returns `rbSet …`; does that claim a write Go does not do, or make a part idle (`rbOwnIn`) without an `Unlock` handed it? | `r` at `lease` is pinned by the ghost element, other names unconstrained (irrelevant); the result is `rbPart` (∃ pending flag), never `rbOwnIn`. Records visible to a reader begun after the `Unlock` (Go check). Lease bucket absent (deleted through the program's own part): Go `lg.Fatal("failed to find a bucket")` (`batch_tx.go:171-176`), an exit, which the model treats as divergence (as the backend's own `UnsafePut.spec`): no counterexample. |
| 6 | **Readers' view: a lease bucket that is not a hook bucket.** If `P.HB "lease" = false`, the lessor's put would change the readers' view (`vData`) without the backend's `bView`, and a `ConcurrentReadTx` read (`thinV`: the reader sees a subset of `vd`) would be proved empty while Go returns the record. `NewLessor`'s `leaseParams` does not say `HB`. | **Blocked**: the axiom quantifies over `d : KBReal`, whose `KBReal.P` fixes `HB n = (n ≠ "key")` (`InvStore.lean:109`), and `isBackend` pins `P` to the backend's location (its mutex invariant). Every lessor backend has `lease` a hook bucket. (A fragile point: a restatement over a general `BParams` would need `HB "lease"` as a premise.) |
| 7 | **Another backend.** `lessorApplyOk` is for every `d`: use it at a `d'` with a different `P`/`γB` and the same location, or at another backend the lessor is not on. | `RW`/`Ln` must lend `lessorBeOn lp d.be`, the user's half of `le.b` (the lock holds the other); a backend location has one `isBackend` (its `isMutex` invariant is allocated once by `New`). `leaseParams` (bucket in the table at id 3, tracked, no hook keys) is required by `NewLessor` and `Recover`, the only writers of `le.b`. |
| 8 | **The hook and `Pk`.** A hook that is `nil` (Go then runs none, so `Pre` is never turned into `Q`), a hook replaced later, `Pk` leaked through the update. | `⌜f ≠ nil⌝ ∗ plHookRO γB f` (frozen: `SetTxPostLockInsideApplyHook` needs the owned half, `backend.go:288`); `csContract`'s update must give `Pk` back; a re-entrant hook (`le.Lookup`, a second `Grant`) deadlocks on `le.mu`. |
| 9 | **Interaction with `Revoke`** (non-monotone lessor): `Revoke` writes `Lease` through the mvcc store's transaction (`le.rd()`), with `le.mu` released during the range deletes. | `Revoke.spec` takes `lessorBeOn` and `storeRb` directly, not `lessorBackend`; a concurrent `Grant` would block on the batch lock holding `le.mu` and `Revoke` then on `le.mu`: a deadlock, no panic. No resource counted by both. |
| 10 | **Persistent facts.** `globalAddr schema.Lease ↦□ bk`; `leaseBatchTx`'s triples persistent. | `schema`'s initializer persists the variable (`Proof/.../schema/Init.lean:258`); Go code could reassign the exported variable, but no proof can (as in `gentokenprefix`). |
| 11 | **`ValidateCalledInsideApply`** (`verify.go:31-38`): with `ETCD_VERIFY=lock` a `LockInsideApply` with a hook set outside `.applyEntries` panics. | A deployment assumption already recorded on its own axiom (`notes/audit.md`, `backend.ValidateCalledInsideApply`); not specific to this statement. |

Not tried: a Lean derivation of `leaseBatchTx` from the real backend's proved specs (it would turn
the statement into a theorem; the thin `Unlock` branch applies because `lease` is a hook bucket);
`NewLessor`'s other conjuncts (`ckptEffectsOk`, `leasesNoExpiry`, the readers' model), pending their
own pass.

## Outside this statement: a lead on the zap axioms

`zap.Logger.Info.spec` (and `Debug`/`Warn`/`Error`/`Fatal`/`Check`) holds for **every** non-nil
`*zap.Logger`; `zap.Logger` is translated with its fields, so a program can allocate `&zap.Logger{}`,
whose `core` is nil, and `Info` panics (`TestZeroLoggerInfo`: nil pointer dereference). Likewise a
logger built with `zap.WithFatalHook(zapcore.WriteThenPanic)` makes `Fatal`, specified `False`
(exits), panic. `notes/audit.md`'s rows argue from what etcd does ("etcd never sets … a fatal
hook"), not from the specs' premise. Not proved here; worth its own `axiom` pass (a likely fix: a
`zapLogger l` predicate given only by `NewNop`/the constructors etcd uses).

## Go checks

`examples/axiomcx/lessorapplyok/lessorapplyok_test.go` (tests only, no Goose project), at
`GOTOOLCHAIN=go1.27.3` and the examples' etcd pin:

```
=== RUN   TestOneLockPerWrite
--- PASS: TestOneLockPerWrite (0.06s)
=== RUN   TestZeroLoggerInfo
    lessorapplyok_test.go:81: panic: runtime error: invalid memory address or nil pointer dereference
--- PASS: TestZeroLoggerInfo (0.00s)
```

## Proposed restatement

None needed. Optional hardening: state `P.HB "lease" = true` (or `leaseParams` with it) where the
contract's soundness depends on it (attack 6), so a later generalisation of `KBReal.P` cannot make
it false silently.
