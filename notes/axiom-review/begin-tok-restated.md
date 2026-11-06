# Review: the begin-tok restatements (reader slots paid by `threadTok`)

Reviewed 2026-11-06, by the `axiom` skill, as an independent reviewer: the six trust-boundary
statements restated on branch `begin-tok`, commit `049391d451` (old → new: `git diff 007725626e
049391d451`), after `notes/axiom-review/backend-snapshot-begin.md` refuted the old `Begin_kv`.

| # | Axiom | Spec file | Verdict |
|---|---|---|---|
| 1 | `bbolt.DB.Begin_kv.wp_proof` | `Spec/go_etcd_io/bbolt/DB__Begin_kv.lean` | **survives** |
| 2 | `bbolt.Tx.Rollback_kv.wp_proof` | `Spec/go_etcd_io/bbolt/Tx__Rollback_kv.lean` | **survives** |
| 3 | `bbolt.Open_kv.wp_proof` | `Spec/go_etcd_io/bbolt/Open_kv.lean` | **survives** |
| 4 | `backend.backend.Snapshot.wp_proof` | `Spec/.../storage/backend/backend__Snapshot.lean` | **survives** (the count; the rest was reviewed earlier: `snapshot.md`, `backend-snapshot-fk.md`) |
| 5 | `backend.snapshot.Close.wp_proof` | `Spec/.../storage/backend/snapshot__Close.lean` | **survives** |
| 6 | `storage.OpenBackend.wp_proof` | `Spec/.../storage/OpenBackend.lean` | **survives** (the count) |

No counterexample was built: no attack got as far as a Go program that panics while the logic
proves it does not. Everything below is reasoning over the pinned sources and Perennial's
definitions. No Go test or Lean build was run.

Pinned sources: bbolt `upamanyus/bbolt` `743299d8cec8`; etcd `upamanyus/etcd` `673da07c8fab`;
go1.27.3; Perennial `84d538063`.

## The claims

1. A read `Begin` takes a `threadTok`. The error branch gives it back. The success branch keeps it
   inside `txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx`. A write `Begin` takes `wrTok` and no token.
2. `Rollback` of `txLive tx 1 ∗ rtxSnap tx D` gives back `txDone tx ∗ threadTok`.
3. `Open` holds under `[ThreadBoundLe GF (2 ^ 29)]`.
4. `Snapshot` takes a `threadTok` and holds under the same instance.
5. `snapshot.Close` of `snapOpenQ sp D γ 1` gives the `threadTok` back.
6. `OpenBackend` holds under the same instance and takes no token. Its goroutine pays for `New`'s.

## How many readers `mmaplock` can have

The fatal needs **exactly `2 ^ 30` readers of one `mmaplock` while a writer is pending**:
- `rwmutex.go:47`: `rwmutexMaxReaders = 1 << 30`.
- `rwmutex.go:129-133`: the fatal fires when `r+1 == 0` after `Lock` subtracted `2 ^ 30`, that is
  when `R = 2 ^ 30`.
- Up to `2 ^ 30 − 1` readers, a writer arriving is safe.

**The tokens** (Perennial `GooseLang/Threads.lean`, `ProgramLogic/Bounds.lean`):
- There are `T − 1` tokens in all, and `threadToks n ⊢ ⌜n < T⌝`.
- `ThreadBoundLe GF (2 ^ 29)` gives `T ≤ 2 ^ 29`.
- Each live forked thread took one unit of fuel. The real thread count stays below `T`
  (`RealThreadsBelow`, `Adequacy.lean:32`).
- A token is not tied to the thread whose fork produced it. `wp_fork_tok` gives it to the forker,
  and a thread holding no token is still live (it just cannot `ThreadExit`). So the logic bounds
  two counts separately:
  - paid readers ≤ tokens ≤ `T − 1`;
  - live threads < `T`.

  It does **not** bound their sum by `T`. It does not need to.

**Unpaid readers.** Every `beginTx` in bbolt at the pin is one of these:
- `db.go:856`: `Begin(false)`, paid by the restated axioms.
- `db.go:1011`: `View`, which no `_kv` axiom or backend spec models. etcd's `backend.Hash` and
  `Defrag` use it, and neither is specified (`bootCfgOk` excludes defrag).
- `db.go:1351`: `freepages`, reached from `Tx.rollback` after a failed commit with
  `NoFreelistSync`, and from `Open`.
- `compact.go:92`: `View`.

Each unpaid one is transient: it is taken and released inside one call, by one thread, with no
user callback in between in any modeled path. So there is at most one per live thread.

**The bound.** R ≤ (T − 1) + (T − 1) ≤ 2 ^ 30 − 2 < 2 ^ 30. The instance is exactly the one that
works: at `2 ^ 30` the same sum could reach the fatal.

The docstrings argue only "tokens < `2 ^ 29` ⇒ readers < `2 ^ 30 − 1`". That omits the transient
readers, which are why the margin is a factor of two (see Suggested fixes).

## Attacks tried

### A1. The old counterexample (one goroutine, `2 ^ 30` read txs, `Close`, `Rollback`)

**Fails.**
- Each `Begin_kv(false)` consumes a `threadTok`, and there are at most `T − 1 ≤ 2 ^ 29 − 1`.
- `Begin_kv` has no instance binder of its own, but it needs `ownDB`. Only `Open_kv` makes
  `ownDB` (`grep ownDB`: `Open_kv`, then `NewAlloc`/`newBatchTxBuffered`/`InvBackend` inside the
  backend), and `Open_kv` is under the instance at the same `GF`.
- No other axiom or premise mints `ownDB`. A hub premise holding `isBackend` must be discharged
  by `OpenBackend`, which is under the instance.

### A2. Tokens from elsewhere: `wp_fork_tok`, forks that never exit, thread pools, levels

**Fails.**
- Forking `n` goroutines that block forever and lend their tokens: each fork takes one unit of
  fuel, so all tokens together stay at `T − 1` however they are gathered.
- A thread pool (`isThreadPoolL`) or a wait group only stores tokens; it creates none.
- Levels: `threadTok` is all `T` levels of one slot, and `levelToks l n ⊢ ⌜n < T⌝` per level. A
  split token cannot be spent twice as a whole one.
- At `threadBound > 2 ^ 30` this attack would work. It is excluded by the instance on `Open_kv`
  (Q2(a)). That is the point of the binder.

### A3. The write branch (`wrTok`)

**Fails.**
- `beginRWTx` (`db.go:913-946`) takes `rwlock`, not `mmaplock`. The spec charges nothing, which
  is right.
- `Rollback_kv` on a writer: the writer's `txLive tx 1` exists (`ownWTxG_live`), but
  `rtxSnap tx D` is only given by a read-mode `Begin_kv`. `Begin_kv` returns `tx` existentially,
  and no axiom equates a writer's `Loc` with an old reader's. So a writer's tx cannot be paired
  with a persistent `rtxSnap` left over from a closed reader.
- A writer's `Commit_kv` may take `mmaplock.Lock()` (`mmap`, `db.go:492`) and, on failure, a
  transient reader (`freepages`). Both are inside the bound above.

### A4. The error branch

**Fails.**
- `beginTx`'s errors release the reader before returning (`db.go:879`, `:886`). The token comes
  back, and the spec says so.
- The write error (`ErrDatabaseReadOnly`, `db.go:916`; not open or not mapped, `:930`, `:936`)
  gives back `wrTok`.
- `Snapshot` has no error branch (`b.lg.Fatal`, an exit, not a panic). This is unchanged and was
  reviewed earlier.

### A5. A second `Rollback_kv`, or a forged one

**Fails.**
- `txLive tx 1` is consumed, and no axiom gives `txLive` back from `txDone`.
- `txLive` is fractional (`txLive_fractional`), so the whole `1` is needed, and no partial share
  can be outstanding (`Bucket_kvr`, `Size_kv` and the rest return their share).
- In Go, a second `Rollback` returns `ErrTxClosed` (`tx.go:305`) and does not `RUnlock`, so it is
  harmless anyway.

### A6. `snapshot.Close` twice, or with shares out

**Fails.**
- `snapOpenQ sp D γ 1` is `□ snapRO sp D γ ∗ ghostVar γ 1 ()`, and `Close` consumes the whole
  share.
- `snapRO` is an `opaque` that nothing but `Snapshot` produces (`grep snapRO`).
- `γ` is already allocated, so no fresh `ghostVar` can be made at it.
- In Go, a second `Close` panics (`close` of a closed `stopc`, `backend.go:1130`), and the spec
  rules it out.
- `WriteTo`/`Size` shares sum to below 1, so `Close` cannot run beside them.

### A7. `Rollback` or `snapshot.Close` after `DB.Close`; `Close` with transactions open

**Fails.**
- `DB.Close` (`db.go:768-779`) takes `mmaplock.Lock()` and blocks until every reader is gone, so
  it cannot return while a paid tx is open. A WP allows the block.
- Rollbacks in other goroutines while `Close` waits: `RUnlock` with a writer pending at
  `R < 2 ^ 30` takes the `readerWait` path, with no fatal.
- `Begin_kv` after `Close_kv` is not available, since `Close_kv` consumes `ownDB`. In Go it would
  take the error branch (`db.go:878`) anyway.

### A8. `Snapshot`'s internal goroutine (`backend.go:393`)

**Fails.**
- Inside the axiom, the fork is a semantic `Fork`, which takes fuel. At zero fuel it stutters
  (`forkStutter`, `Lifting.lean`), so `Snapshot` never returns. Partial correctness covers that.
- Snapshots cannot pile up: each one costs a caller token (R ≤ `T − 1` paid), and each warning
  goroutine is a live thread under `T`.
- Net, the caller is out one token per open snapshot until `Close`, as the docstring says. Its
  wording is not quite right: the goroutine is paid by its own fork's fuel, and the caller's token
  pays the slot (see Suggested fixes).
- The goroutine always ends at `Close`'s `close(stopc)`/`<-donec` (`:1130-1131`).

### A9. `OpenBackend`'s goroutine and the backend's long-lived reader (the coordinator's questions)

**Accounting** (the drafter's design, checked against `wp_fork_tok`'s semantics):

1. `OpenBackend` forks G (`backend.go:79`): fuel −1, token `a` to G (`wp_fork_tok_body`).
2. G calls `New`. `newBatchTxBuffered` consumes `a` into `readTx.tx`.
3. `go b.run()` (`wp_fork_tok_self`): fuel −1, token `b` to G.
4. `New` returns `b`. G sends on `beOpened` and exits with `b`: fuel +1.

Net: fuel −1. The `run` goroutine is live and holds no token. `a` pays `readTx.tx`'s slot.

**Q1: is the accounting right?** Yes, for the bound that matters. The thread bound counts the
`run` goroutine (it took fuel, and real threads stay below `T`). The token count bounds the
reader. One unit of fuel thus stands behind both a live thread and a reader slot. That is
legitimate in Perennial: a token is not the thread's identity, and a thread without one simply
cannot exit, which is why `run` can exit only after `CommitAndStop` gives it the last read tx's
token.

The bound then needs paid readers ≤ `T − 1` and transient readers ≤ live threads < `T`, as above.
It does not need one slot per thread *and* per reader.

Rotation at each commit (`batch_tx.go:391-397`):
- the rollback goroutine's fork token pays the new `readTx.tx`;
- the old tx keeps its token, which the goroutine gets back from `Rollback_kv` and exits with.

`n` pending rollback goroutines (held up by an unreleased `ConcurrentReadTx` on `txWg`) are
`n + 1` open bbolt read txs paid by `n + 1` tokens. So a reader pile-up is bounded by the tokens.

This is the plan's design (`notes/begin-tok-plan.md` §2). Its proofs (`unsafeCommit`,
`newBatchTxBuffered`, `run`, `newBackend`) are not finished on the branch, and this review cannot
check them. What it checks is that the axioms make that design possible and no more.

**Q2: many backends, or reopen after `Close`?** **Fails.**
- `mmaplock` is per `*bolt.DB`. Readers on different databases do not add up.
- Two opens of one file need `fileHolds path D` twice, which is exclusive and consumed by
  `Open_kv`/`OpenBackend`. In Go the second `Open` would block on the file lock (`flock`) anyway.
- Reopen after `Close`: `DB.Close` waits for every reader of the old database (A7), and the new
  database has a fresh `mmaplock`.
- `OpenBackend`'s goroutine is always joined: both `select` arms end in a receive from `beOpened`
  (`backend.go:87-99`), so G never outlives the call.

### A10. Nested or callback-held transient readers

**Not applicable to the six.**
- An unpaid reader held across a user callback could nest: `backend.Hash(ignores)` runs `ignores`
  inside `db.View` (`backend.go:430`), and a recursive `ignores` stacks readers.
- No modeled path does that today: `Hash` and `Defrag` have no spec.
- **If either is ever specified, it must charge a token per nesting level, or the sum above
  fails.** Recorded as a hazard for the gate (`begin-tok-plan.md` §5), whose holder scan works per
  function and would not see a reader held across a callback.

## Citations (checked against the pins)

All the line numbers point at the code they name:
- bbolt: `db.go:841`, `:866`, `:875`, `:879`, `:886`, `:951`, `:492`, `:768-779`; `tx.go:303`,
  `:313`, `:353`, `:378`;
- etcd: `backend.go:381`, `:385`, `:386`, `:393`, `:1129`, `:1131`, `:1132`;
  `server/storage/backend.go:79`;
- go1.27.3: `sync/rwmutex.go:47`, `:130-132`.

Nits:
- **Mixed conventions.** `Begin_kv`'s and `Rollback_kv`'s chain `tx.go:303 → :313 → :353 → :378`
  cites definitions for `nonPhysicalRollback`/`close` (the calls are at `:308` and `:320`) but a
  call site for `removeTx` (`:378`).
- **`Begin_kv`'s Proof docstring** says "`mmaplock`'s only uses are `db.go:492, :775, :875-886,
  :951`". That is true of the field, but `freepages` (`db.go:1351`) and `View` (`:1011`) also take
  a reader through `beginTx`. Those are the transient readers the bound has to absorb.
- **"one more with a writer pending fatals"** (`Begin_kv`'s Proof docstring). Imprecise: the fatal
  is at exactly `2 ^ 30` readers when the writer subtracts, on the next `RUnlock`. It is not a
  "`2 ^ 30` + 1"-th reader.

## What the statements claim that Go does not do

Nothing found. One small idealization, already in the old statements and unchanged here:
`Begin_kv`'s read branch returns `isDB db` and keeps `ownDB` while the tx is open, whatever the
database's `opened` state. `ownDB` is consumed by `Close_kv`, so that is consistent.

## Suggested fixes (not applied)

1. **Make the margin argument the right one.** In `Open_kv`'s docstring (and `Begin_kv`'s Proof
   docstring), replace "fewer than `2 ^ 29` live threads keeps the readers below `2 ^ 30 − 1`"
   with:

   > paid readers ≤ tokens < `2 ^ 29`, and bbolt's transient readers (`View`, `freepages`: one
   > per live thread, released within the call) < `2 ^ 29`, so readers < `2 ^ 30`.

   This says why `2 ^ 29` and not `2 ^ 30`.
2. **Fix `Snapshot`'s docstring (Q4 sentence).** "The same token pays for it" should read: "the
   warning goroutine is a live thread, paid by its fork's fuel. The caller's token pays the reader
   slot. Net one token per open snapshot until `Close`." In Perennial a fork always draws its own
   fuel, so a caller's token never pays for a goroutine.
3. **Make the gate (`begin-tok-plan.md` §5) note the A10 hazard.** A trust-boundary axiom that runs
   a caller's callback inside `db.View`/`Begin` must charge per call. The holder scan does not
   catch this, since such a function releases its reader before returning.
4. **Make the citation chain consistent** (all call sites or all definitions), and add `db.go:1011`
   and `:1351` to the list of `beginTx` reader takers.
