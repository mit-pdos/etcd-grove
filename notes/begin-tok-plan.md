# begin-tok: bbolt's read transactions and the backend's snapshots pay for their reader slot

The stage that fixes the soundness bug of `notes/STATUS.md`, "Soundness bug: `bbolt.DB.Begin_kv`'s
read transactions take an unpaid reader slot" (refutation: `notes/axiom-review/backend-snapshot-begin.md`;
the decision: `notes/decisions.md`, "bbolt's read transactions and the backend's snapshots pay for
their reader slot"). Branch `begin-tok`, worktree `/shared/etcd-grove-axbk`, off `lean` `007725626e`.

## Scope (2026-11-06)

Design only: no Lean or Go was edited and nothing was built. Line numbers are at `007725626e`.

### 1. Retire or restate

**What the two layers give.**

| | `_kv` family (what the backend uses) | proved API (`Spec/go_etcd_io/bbolt/Api.lean`) |
|---|---|---|
| database | `ownDB db γ D`, opaque axiom, exclusive (`InvBbolt.lean:89`) | `isBolt db γ` (persistent) `∗ boltState γ q D` (fractional, client-owned) |
| read tx | `txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx` (opaque) | `boltTx tx γ 1 (ro D)` (sealed) |
| reader slot | none | `DB.Begin.spec` takes `threadTok` (lent to `mmaplock`'s pool), `Tx.Rollback.spec` returns it |
| bound | none | `Open` takes `[ThreadBoundLe GF (2 ^ 29)]` (D3) |
| other premises | none | `[HasExt osFsExt]` on every triple (D8, round 12) |

**The callers.** `grep -rn 'Begin_kv'` (outside `old/`, `.lake/`):
- `Proof/go_etcd_io/etcd/server/v3/storage/backend/backend__unsafeBegin.lean:36,45`: the only
  caller, in both modes (`w` is a variable). `unsafeBegin` is called only by `backend.begin`
  (`backend__begin.lean`), whose read-mode callers are:
  - `newBatchTxBuffered.lean:90` (the first read transaction, `readTx.tx` nil before);
  - `batchTxBuffered__unsafeCommit.lean:172,211` (the new interval's read transaction, after the
    old one is handed to the rollback goroutine).
  (`batchTx__commit.lean:140` and `newBatchTxBuffered.lean:84` are write mode.)
- `examples/axiomcx/bboltnan/Run.lean:101` (write mode, `Run.lean:71,166`: the NaN counterexample).
- `backend.Snapshot`'s own `b.db.Begin(false)` (`backend.go:386`) is inside the axiom, not a call
  of `Begin_kv`.

`Rollback_kv`: one caller, the rollback goroutine forked in `batchTxBuffered__unsafeCommit.lean:155-158`
(`wp_fork`, then `wp_rollback_Wait`, then `hRollback`). `snapshot.Close` rolls back inside its axiom.
The `concurrentReadTx`/`readTx` readers open no bbolt transaction: they share `readTx.tx` through
`txWg` (`rdShare`, `InvBackend.lean:770`).

**Can the backend use `DB.Begin.spec` for its reads only?** No, not without the whole backend switch
(`notes/bbolt-coordinator-handoff.md`, step 3):
- `DB.Begin.spec` needs `isBolt db γ` and an atomic update over `boltState`. The backend holds the
  opaque `ownDB`, which is not tied to either. Tying them takes either the switch's definition
  `ownDB db γ D := isBolt db γ ∗ boltState γ 1 D` (then every `_kv` axiom must be re-derived, since
  `ownDB` stops being opaque under them) or a bridge axiom equating two models of one database, a new
  and riskier trust assumption than the one being fixed.
- The transaction it returns is `boltTx tx γ 1 (ro D)`, but the backend's reads go through
  `Tx.Bucket_kvr`, `Bucket.Cursor_kvr`, `Cursor.Seek_kv`, `Cursor.Next_kv`, `Tx.Size_kv`, `Tx.DB_kv`,
  `DB.Info_kv` and `Rollback_kv`, all over `txLive`/`rtxSnap`/`rtxStats`. Each would be restated over
  `boltTx`, which is the switch's table (`bbolt-spec-decisions.md`, "The backend: each `_kv` axiom
  against the new specs").
- The switch also brings `[HasExt osFsExt]` to every backend spec and every etcdserver spec above it
  (round 12, review 11 L3), `statSlot` for `Stats` (D2), `bboltEntryMax` from mvcc (D4) and
  `BNames.db : BoltName`. That changes many statements up to the hubs.

**Recommendation: restate (option B).**
- `Begin_kv`'s read half takes a `threadTok`. `Rollback_kv` gives it back. `Open_kv` takes D3's
  instance.
- The restated rows have exactly the shape of the proved `DB.Begin.spec`/`Tx.Rollback.spec`:
  - read mode takes `threadTok`;
  - the error branch gives it back;
  - `Rollback` returns `if T.rw then emp else threadTok`;
  - `Open` is under `ThreadBoundLe GF (2 ^ 29)`.

  So the backend switch derives them as corollaries later, and nothing done here is thrown away.
- The token flow inside the backend needs no new invariant (§2).

### 2. The token flow

The rule (`notes/bounds-plan.md`, "The rule"): a client holds only `threadTok`s; the owner (bbolt, of
`mmaplock`) turns the count into a protocol. bbolt's `_kv` layer is opaque, so the restated axioms
state the protocol directly: a token goes in at `Begin(false)`/`Snapshot`, and one comes out at
`Rollback`/`snapshot.Close`. The flow uses Perennial's `wp_fork_tok`/`wp_fork_tok_self`
(`.lake/packages/perennial/Perennial/GooseLang/Lifting.lean:1964,2006`): at a `go` statement the
forking thread receives a fresh token, and the forked thread must exit holding one.

**No existing pool pays for an `mmaplock` slot**, and none is needed:
- `rdPoolN`, `bkRPool`, `rdAuth` and `rdStockN` (`RdPool.lean:49-63,137`) are slots of the backend's
  own `readTx.mu`/`txMu` (`rdTok`), not of bbolt's `mmaplock`.
- They count the backend's readers of the shared `readTx.tx`. That transaction is one bbolt reader
  per interval, whatever the number of backend readers.
- So they stay as they are, and they are not borrowed from.

Each site:

| site | Go | where the token comes from | change |
|---|---|---|---|
| first read tx | `newBackend` → `newBatchTxBuffered` → `tx.Commit()` → `begin(false)` (`readTx.tx` nil, no rollback fork) | the creator's own `threadTok` (`newBackend`'s pre) | `newBatchTxBuffered.spec` pre `+ threadTok` (consumed into the tx) |
| `go b.run()` | `newBackend` (`backend.go:277`) | `wp_fork_tok_self`: the creator gets the fresh token back. `run` must exit with one | `newBackend.spec`/`New.spec`: pre `+ threadTok`, success post `+ threadTok` (net zero for the caller) |
| interval rotation, not stopping | `unsafeCommit(false)`: `go func(){wg.Wait(); tx.Rollback()}`, then `readTx.tx = begin(false)` | `wp_fork_tok`: the committer gets the fresh token and gives it to `begin(false)`. The rollback goroutine exits with the token `Rollback_kv` returns (the old tx's) | proof only (`unsafeCommit.lean:155`). `rollbackRes` unchanged: `txLive ½ ∗ rtxSnap` plus the wait group's half are enough for `Rollback_kv` |
| interval rotation, stopping | `CommitAndStop` → `unsafeCommit(true)`: rollback fork, no new `begin` | the fork's fresh token stays with `run` | `unsafeCommit.spec`/`batchTxBuffered.commit.spec` post `+ (if stop then threadTok else emp)`; `CommitAndStop.spec` post `+ threadTok`; `run.spec` post `True` → `threadTok` |
| `ConcurrentReadTx`, `ReadTx` readers | share `readTx.tx` (`txWg`) | none: no bbolt transaction | none |
| `backend.Snapshot` | `b.db.Begin(false)` (`backend.go:386`), held until `snapshot.Close` (`:1132`) | the caller's `threadTok` | `Snapshot.spec` pre `+ threadTok`; `snapshot.Close.spec` post `True` → `threadTok` |
| its warning goroutine (`backend.go:393`) | lives until `Close`'s `<-donec` | inside the axiom. It is a live goroutine, so it is paid by the fork's fuel like every goroutine. One token per open snapshot bounds both the slot and the goroutine, since they live and die together (review's proposal) | none beyond the row above |
| snapshot sender | `applyAll`'s `msgSnapC` branch → `createMergedSnapshotMessage` → `s.be.Snapshot()`, then `newSnapshotReaderCloser`, whose goroutine streams and calls `snapshot.Close()` | the apply thread's token from `srvGoRes` (`InvGoAttach.lean:161`: `srvWgReader ∗ threadTok`), unfolded around the call as `ApplyAllSnap.lean:181,203` already does for `applySnapshot`. `newSnapshotReaderCloser`'s `go` uses `wp_fork_tok_self`: the apply thread gets the fresh token back, and the goroutine exits with `Close`'s. Net zero for the apply thread | `srvBeSnapOk`'s triple (`InvSnapSend.lean:55`) pre `RS` → `RS ∗ threadTok`; `createMergedSnapshotMessage.spec` pre/post `+ threadTok`; `newSnapshotReaderCloser.spec` post `+ threadTok` (outside the wand) |
| maintenance `Snapshot` | `v3rpc.authMaintenanceServer.Snapshot` | none: the inner `maintenanceServer.Snapshot` is names-only (`guardedSnapOk`) and does not reach `backend.Snapshot` | none |
| defrag | `backend.Defrag` | not modeled: `bootCfgOk` excludes bootstrap defrag (`InvBoot.lean:239-243`), and no verified caller | none |
| mvcc store/restore | `store.restore`, `NewStore`: read through `ReadTx`/`ConcurrentReadTx` | none: no bbolt transaction of their own | none |
| server hubs | backend opened by `bootstrap` (contract, `InvBoot.lean:503`) → `OpenBackend` → its goroutine → `New`; and by `applySnapshot` → `OpenSnapshotBackend` → `OpenBackend` | `OpenBackend`'s own goroutine pays for `New` with its fork token (`wp_fork_tok_body`), and gets it back from `New` | `OpenBackend`'s triple unchanged; its docstring's argument names the token. The instance: §3 |

**New pool slots needed: none.** Every token is a thread's own, or a fork's fresh one, and each
returns to a thread that exits with it. No owner gains a protocol, so there is no new
`threadPool`.

### 3. Every statement that changes

**Trusted axioms** (same names: the trust base's count and names do not change, 817 axioms):

1. `bbolt.DB.Begin_kv` (`Spec/go_etcd_io/bbolt/DB__Begin_kv.lean:31`):
   - pre `ownDB db γ D ∗ (if w then wrTok γ else iprop(True))` →
     `ownDB db γ D ∗ (if w then wrTok γ else threadTok)`;
   - error branch `(if w then wrTok γ else iprop(True))` → `(if w then wrTok γ else threadTok)`;
   - success branch unchanged. The token is held by the transaction: no new predicate.
2. `bbolt.Tx.Rollback_kv` (`Tx__Rollback_kv.lean:29`):
   - post `txDone tx` → `txDone tx ∗ threadTok`.
   - Sound because the pre is the whole `txLive tx 1` plus `rtxSnap tx D`, which only a read-mode
     `Begin_kv` gives (a writer never has `rtxSnap`). `txLive tx 1` is consumed, so each paid token
     is returned once.
   - Alternative: an opaque `rtxSlot tx` in `Begin_kv`'s post, consumed here. It adds a predicate
     axiom and buys nothing over the pairing (Q3).
3. `bbolt.Open_kv` (`Open_kv.lean:40`): a leading instance binder `∀ [ThreadBoundLe GF (2 ^ 29)]`
   (D3's value). This is a stronger premise, so a weaker axiom. Without it:
   - a single thread can collect `2 ^ 30` tokens by forking `2 ^ 30` goroutines that never exit;
   - at `threadBound ≥ 2 ^ 30 + 1` the restated axioms would still be false of the semantics;
   - in Go that run is stuck (about 2 TiB of goroutines), the same idealization as `Snapshot`'s
     (Q2).
4. `backend.backend.Snapshot` (`backend__Snapshot.lean:61`):
   - pre `+ threadTok`;
   - a leading `∀ [ThreadBoundLe GF (2 ^ 29)]` (Q2).
5. `backend.snapshot.Close` (`snapshot__Close.lean:33`): post `True` → `threadTok`. The same pairing
   argument: `snapOpenQ sp D γ 1`'s `ghostVar γ 1 ()` is exclusive and comes only from `Snapshot`.
6. `storage.OpenBackend` (`Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean:48`):
   - a leading `∀ [ThreadBoundLe GF (2 ^ 29)]`, because its argument is `New`'s, which is now under
     the instance;
   - the triple is unchanged;
   - the docstring (`Proof/.../storage/OpenBackend.lean:27`) says the goroutine pays `New`'s token.
7. Unchanged: `DB.Close_kv` (`Close` blocks until the readers end, which a WP allows; with the
   tokens and the bound there is no fatal), and the other 16 `_kv` triples.

**Proved specs that change** (backend-internal unless marked API):

| spec | file:line | old → new |
|---|---|---|
| `backend.unsafeBegin` | `Spec/.../backend/backend__unsafeBegin.lean:26` | pre `(if w then wrTok γd else iprop(True))` → `(if w then wrTok γd else threadTok)` |
| `backend.begin` | `backend__begin.lean:26` | the same |
| `newBatchTxBuffered` | `newBatchTxBuffered.lean:33` | pre `+ threadTok` |
| `batchTxBuffered.unsafeCommit` | `batchTxBuffered__unsafeCommit.lean:26` | post `+ (if stop then threadTok else emp)` |
| `batchTxBuffered.commit` | `batchTxBuffered__commit.lean:26` | post `+ (if stop then threadTok else emp)`. Callers at `stop = false` (`Commit`, `Unlock`) reduce it to `emp` |
| `batchTxBuffered.CommitAndStop` | `batchTxBuffered__CommitAndStop.lean:26` | post `+ threadTok` |
| `backend.run` | `backend__run.lean:26` | post `True` → `threadTok` |
| `newBackend` | `newBackend.lean:41` | `∀ [ThreadBoundLe GF (2 ^ 29)]`; pre `+ threadTok`; success post `+ threadTok` |
| `backend.New` | `New.lean:30` | the same (not in `etc/api/backend.txt`: no interface diff) |
| `storage.OpenSnapshotBackend` | `Spec/.../storage/OpenSnapshotBackend.lean:46` | `∀ [ThreadBoundLe GF (2 ^ 29)]` (it calls `OpenBackend`) |
| `newSnapshotReaderCloser` | `Spec/.../etcdserver/newSnapshotReaderCloser.lean:37` | post `(snapOpenQ … ½ -∗ readerStreams …)` → `threadTok ∗ (snapOpenQ … ½ -∗ readerStreams …)` |
| `EtcdServer.createMergedSnapshotMessage` | `EtcdServer__createMergedSnapshotMessage.lean:37` | pre `+ threadTok`, post `+ threadTok` |
| `srvBeSnapOk` (def) | `Proof/.../etcdserver/InvSnapSend.lean:55` | `{{ RS }} … Snapshot …` → `{{ RS ∗ threadTok }} …`. Lemma `srvBeSnapOk_of_backend` (`SnapSendBranch.lean:94`) gains the instance binder |

The interfaces to regenerate:
- bbolt: `interface/Spec/go_etcd_io/bbolt/{DB__Begin_kv,Tx__Rollback_kv,Open_kv}.txt`;
- backend: `interface/Spec/go_etcd_io/etcd/server/v3/storage/backend/{backend__Snapshot,snapshot__Close}.txt`.

`Link.lean` files: unchanged. Each spec takes its instance as a leading binder, and no proof gains or
loses a callee.

**Server hub statements: none changes.** Each was checked:
- `NewServer.spec`: `Spec/.../etcdserver/NewServer.lean:244` (`threadTok` in), `:311-312` (out).
  The backend at boot is `bootOk`'s, from `bootstrapContract` (`InvBoot.lean:503`, unchanged:
  `OpenBackend`'s goroutine pays). The bound is the existing `:195`, `threadBound GF ≤ rdPoolN`.
- `isServerM` (`AppliedOn.lean:301`, bound `:306`), `srvBuiltG` (`ServerOn.lean:449`, `%Hbound`
  `:519`), `isServerBuilt` (`InvStart.lean:229`), `isServerBuiltOn`/`M` (`StartOn.lean:69,146`),
  `isServerBuiltC`/`isServerRunC` (`AuthCompRows.lean:122,214`), `isServerRun` (`InvRun.lean:40`),
  `isServerRunOn` (`RunOn.lean:86`), `isServerApplyAll` (`InvApplyAll.lean:119`): none mentions a
  changed spec or `srvBeSnapOk`. The instance `ThreadBoundLe GF (2 ^ 29)` is derived locally from
  their existing `threadBound GF ≤ rdPoolN` (`2 ^ 28`).
- `EtcdServer.applySnapshot.spec` (`:146`, `:215`, `threadTok` in and out, already there) and
  `EtcdServer.applyAll.spec`: unchanged. The token for `createMergedSnapshotMessage` is unfolded
  from `srvGoRes` inside the proofs.
- etcdstart: no file mentions a changed name. Checked with a grep of `Results`/`Adequacy`/`Main`/
  `Linked`/`etcdstart`/`cluster3` for every name above.

**So the coordinator has nothing to sequence at the hub.**
- The proof files edited inside etcdserver are `ApplyAllSnap.lean`, `ApplyAllSnapOn.lean`,
  `EtcdServer__applyAll.lean`, `SnapSendBranch.lean`, `SnapApplyWalk.lean`/
  `EtcdServer__applySnapshot.lean` (one `haveI` each for `OpenSnapshotBackend`'s instance),
  `newSnapshotReaderCloser.lean`, `EtcdServer__createMergedSnapshotMessage.lean` and
  `InvSnapSend.lean`.
- Edits there can conflict textually with R2d' or restart work in the same files.

**Closed theorems: none expected to change.** No `Results.lean`, adequacy or example `Main`
mentions a changed name. The changed pres are met inside proofs.

One example statement changes: `examples/axiomcx/bboltnan/Run.lean` (a counterexample, not a
result) calls `Open_kv`, so its section gains `[ThreadBoundLe GF (2 ^ 29)]`.

### 4. Bounds

- **No count changes:** `rdPoolN = 2 ^ 28`, `authRdN`, `rdStockN = 536870783`
  (`RdPool.lean:49-80`), `srvStartReadN`, `srvRevokePoolN` and the `2 ^ 28` thread bound all stay.
- `notes/revoke-open-plan.md` §K's consumers split `read.mux`'s slots, which this stage does not
  touch. No new stock or replicate appears (the 80 GB `[∗list] replicate 2 ^ 28` hazard does not
  arise).
- `etc/bounds-check.py`: `ThreadBoundLe` does not match `spec-thread`'s `\bthreadBound\b`. The
  `haveI`s are in Proof files. The baseline is unchanged.
- `notes/bounds-plan.md`'s "Known gap" section is closed by this stage. The note there should say
  so.

### 5. The gate: `etc/reader-slot-check.py` (in `etc/gates.sh` beside `errorf-wrap-check.py`)

What it checks: **a trust-boundary axiom whose Go function holds an `RWMutex` reader slot past its
return charges a token for it, and its closer gives one back.**

1. **The slot holders, from the translations.** For each function body in `Code/**.lean` (and a
   part's `<root>/Code/`):
   - count the `RLock` calls (`@!! go!"RLock"`) and the `RUnlock` calls, deferred or not, on the same
     receiver expression. More `RLock`s than `RUnlock`s makes it a holder (bbolt's `DB.beginTx`,
     `db.go:875` vs `:951`).
   - A function that calls a holder and does not call its registered releaser is a holder too,
     computed as a fixed point over the call graph, across packages. This gives `DB.Begin`, and
     through it `backend.Snapshot`.
2. **The axioms.** Every `axiom <F>.wp_proof` under `Proof/` maps to its Go function by the layout
   (`Spec/<pkg>/<T>__<M>.lean`). If `<F>` is a holder, its spec's code (comments stripped) must
   mention `threadTok`, `levelTok`, or a slot predicate from an allow list (`rdTok`, `ownThreadLoan`).
3. **The closers.** A pair file `etc/reader-slot-pairs.txt` lists each holder axiom with its closer
   axiom (`bbolt.DB.Begin_kv` ↔ `bbolt.Tx.Rollback_kv`, `backend.backend.Snapshot` ↔
   `backend.snapshot.Close`). The closer's post (the text after `RET`) must mention the same token.
   A holder axiom with no pair fails.
4. **Exceptions**: `etc/reader-slot-allow.txt`, `NAME  # why`, as in `errorf-wrap-check.py`'s
   `REVIEWED`.
   - Names-only packages have no bodies to scan. The script prints their axioms as unscanned
     (informational, not a failure), so the reader sees the gate's reach.
   - Exit 1 on an unpaid holder axiom, a missing pair, or a closer without the token.

It is a cheap name-level check, not a proof, as `errorf-wrap-check.py` is. **Acceptance:**
- run on `lean` `007725626e`, it must fail and name `bbolt.DB.Begin_kv` and
  `backend.backend.Snapshot`;
- on the branch, it passes.

Its first run may flag other axioms. Each is triaged: a new finding, recorded as the
soundness-bug section was, or an allow-list entry with its reason (§7).

Placement: a script of its own. `bounds-check.py`'s per-package regex counts cannot express "holder
axiom without a token". A line in `bounds-check.py`'s report pointing to it would do.

### 6. Estimate and order of work

**Files.**
- Trusted specs, with their axiom files' docstrings: 7 specs, 6 axiom files.
- Backend specs and proofs: 10 specs, about 12 proofs (`unsafeBegin`, `begin`, `newBatchTxBuffered`,
  `unsafeCommit`, `batchTxBuffered.{commit,Commit,Unlock,CommitAndStop}`, `run`, `newBackend`,
  `New`).
- `storage/OpenSnapshotBackend` proof.
- etcdserver: 2 specs, about 8 proofs and defs (§3).
- `bboltnan/Run.lean`.
- The gate: the script, its pairs and allow files, and a line in `gates.sh`.
- Notes: `decisions.md` ("As built"), `STATUS.md`, `bounds-plan.md` (gap closed),
  `bbolt-spec-decisions.md` (D1 applied at the `_kv` layer), and an `axiom-review` report.
- About 40 files in all.

**Rebuild** (`etc/importers.py --count`, at `007725626e`):

| changed modules | importers |
|---|---|
| the three bbolt `_kv` specs | 422 modules / 83k lines |
| the backend's internal specs | 432 / 84k |
| `New` | 415 / 82k |
| `Snapshot` + `snapshot.Close` | 749 / 150k |
| `OpenBackend`/`OpenSnapshotBackend` | 431 / 87k |
| the server's snapshot path (2 specs + `InvSnapSend`) | 752 / 150k |
| **all together** | **805 modules / 158k lines** |

Most of them are `Link`/`Results` and the examples above them, which recompile without edits. Run
builds under the `systemd-run MemoryMax` cap.

**Order of work.**
1. Trusted statements and their docstrings (§3, items 1-6). Then an `axiom`-skill review of the
   restated set. Attacks:
   - a second `Rollback_kv`;
   - a `Rollback_kv` on a writer's `txLive`;
   - a forged `snapOpenQ`;
   - the many-forks variant against the instance.
2. Backend: `unsafeBegin` → `begin` → `newBatchTxBuffered` → `unsafeCommit` (`wp_fork_tok`) →
   `commit`/`Commit`/`Unlock`/`CommitAndStop` → `run` → `newBackend` (`wp_fork_tok_self`) → `New`.
   Build the backend's `Link`.
3. `OpenSnapshotBackend` and the `applySnapshot` chain's `haveI`.
4. Server snapshot path: `newSnapshotReaderCloser` (`wp_fork_tok_self`) → `srvBeSnapOk`/
   `SnapSendBranch` → `createMergedSnapshotMessage` → the three `applyAll` files.
5. `bboltnan` (the instance). Full build.
6. The counterexample, in a scratch worktree of `axiom/backend-snapshot-begin` (`f37d8ce925`) merged
   with `begin-tok`. `Proof/.../axiomcx/bboltrd/Run.lean` must fail at the loop's `Begin_kv` (no
   `threadTok`) and at `Open_kv` (no instance). Record the error in the axiom-review report. Then
   delete the scratch worktree. Nothing of it lands.
7. The gate (§5), first against `lean` (must fail), then on the branch.
8. `etc/tcb-report.py --check`: expected unchanged (the same 817 axiom names, 4 `sorry`s); then
   `--check --update` only if it moves. Collections likewise.
9. Regenerate the interfaces (bbolt, backend). `etc/gates.sh`. Notes. Land with `etc/land.sh`.

### 7. Risks and open questions

**Questions for the user**:
- **Q1 (retire or restate).** Recommend restate (§1). Retiring needs the full backend switch, and
  its `[HasExt osFsExt]` premise reaches every etcdserver spec. The restated axioms are exactly
  what the switch would derive later.
- **Q2 (the instance).** Should `Open_kv`, `Snapshot`, `OpenBackend`, and hence `newBackend`/`New`/
  `OpenSnapshotBackend`, take `[ThreadBoundLe GF (2 ^ 29)]`?
  - (a) Yes: the axioms become true of the semantics at every `GF`. Costs: the binders, and a
    `haveI` at the server's two call paths.
  - (b) Tokens only: `bboltrd` still fails, but a many-forks variant (`2 ^ 30` goroutines that
    never exit, each lending main its token) would verify at `threadBound > 2 ^ 30`. It is stuck in
    Go, like every thread-bound idealization.

  **Recommend (a).** It matches the proved `Open` (D3), so the switch is free later.
- **Q3 (where the token lives).** Recommend the pairing: `Rollback_kv`/`snapshot.Close` return a
  `threadTok`, and no new predicate. This mirrors `Tx.Rollback.spec`. The alternative, an opaque
  `rtxSlot tx`, is one more trusted predicate.
- **Q4 (`Snapshot`'s goroutine).** Recommend one token per snapshot, paying for the read
  transaction's slot. The warning goroutine is a live thread, paid by its fork. That is the
  review's argument: they live and die together.

**Risks**:
- The gate's first run may flag other trust-boundary axioms that hold a reader slot (unknown today;
  the review's grep of backend and bbolt found only these two). Each one found is a finding to
  record, not something to allow-list silently. It can grow the stage.
- `unsafeCommit`'s proof is long, and the fork is mid-proof (`:155`). Switching `wp_fork` to
  `wp_fork_tok` changes the forked goal's post to `threadTok`; the rest of the proof is unchanged.
- `run`'s loop (`wp_for`) must carry the absence of a token until the stop. Its only exit is
  through `CommitAndStop` (`backend__run.lean:154`), so the token appears exactly where the post
  needs it.
- Conflicts: proof-level only. The etcdserver files listed in §3 may also be edited by R2d' and the
  restart work. No hub statement changes.
- The memory cap: the server's applyAll files are among the larger compiles. Build under the cap.

## Draft (2026-11-06)

Built on branch `begin-tok` (worktree `/shared/etcd-grove-axbk`). Commits: `049391d451` (the trusted
statements alone, for the independent axiom review), `c7b1a35a28` (the backend, `OpenSnapshotBackend`,
`bboltnan`), then the server's snapshot path. Every statement change, old → new:

**Trusted** (the same axiom names; docstrings cite bbolt `743299d8cec8` `db.go:875` RLock, `:879/:886`
error-path RUnlocks, `:951` RUnlock in `removeTx`, `tx.go:303→313→353→378`; etcd `backend.go:386`,
`:393`, `:1131-1132`; `storage/backend.go:79`):

| axiom | old → new |
|---|---|
| `bbolt.DB.Begin_kv` | pre `(if w then wrTok γ else iprop(True))` → `(if w then wrTok γ else threadTok)`; error branch the same |
| `bbolt.Tx.Rollback_kv` | post `txDone tx` → `txDone tx ∗ threadTok` |
| `bbolt.Open_kv` | `∀ (path …)` → `∀ [ThreadBoundLe GF (2 ^ 29)] (path …)`; triple unchanged |
| `backend.backend.Snapshot` | `∀ [ThreadBoundLe GF (2 ^ 29)]` added; pre `… wbTok γ ∗ R ∗ …` → `… wbTok γ ∗ threadTok ∗ R ∗ …` |
| `backend.snapshot.Close` | post `True` → `threadTok` |
| `storage.OpenBackend` | `∀ [ThreadBoundLe GF (2 ^ 29)]` added; triple unchanged |

**Internal** (backend, storage, etcdserver; the generated interfaces of `etc/api/{bbolt,backend}.txt` change only in these functions' spec and proof files, regenerated; no API module changes):

| statement | old → new |
|---|---|
| `backend.unsafeBegin.spec`, `backend.begin.spec` | pre `(if w then wrTok γd else iprop(True))` → `(if w then wrTok γd else threadTok)` |
| `backend.newBatchTxBuffered.spec` | pre `… ∗ wrTok γd` → `… ∗ wrTok γd ∗ threadTok` |
| `batchTxBuffered.unsafeCommit.spec`, `batchTxBuffered.commit.spec` | post's stop branch `… ∗ bStopped γ ∗ bDBOutG γ P` → `… ∗ bDBOutG γ P ∗ threadTok` |
| `batchTxBuffered.CommitAndStop.spec` | post `bStopped γ ∗ bDBOut γ P W Pk ∗ Y` → `… ∗ Y ∗ threadTok` |
| `backend.run.spec` | post `True` → `threadTok` |
| `backend.newBackend.spec`, `backend.New.spec` | `∀ [ThreadBoundLe GF (2 ^ 29)]` added; pre `+ threadTok`; success post `… ∗ bFile γ cfg.Path'` → `… ∗ bFile γ cfg.Path' ∗ threadTok` |
| `storage.OpenSnapshotBackend.spec` | `∀ [ThreadBoundLe GF (2 ^ 29)]` added |
| `newSnapshotReaderCloser.spec` | post `snapOpenQ … ½ -∗ readerStreams …` → `threadTok ∗ (snapOpenQ … ½ -∗ readerStreams …)` |
| `EtcdServer.createMergedSnapshotMessage.spec` | pre `… ∗ epCsOk cs` → `… ∗ epCsOk cs ∗ threadTok`; post `… ∗ srvBeAddr s ↦{dq} be ∗ ∃ …` → `… ∗ srvBeAddr s ↦{dq} be ∗ threadTok ∗ ∃ …` |
| `srvBeSnapOk` (def, `InvSnapSend.lean`) | `{{ RS }}` → `{{ RS ∗ threadTok }}` |
| `srvBeSnapOk_of_backend`, `srvBeSnapOk_window` | a leading `[ThreadBoundLe GF (2 ^ 29)]` |
| `backend.backend.Snapshot.spec_of_specF2` | its statement `∀ [ThreadBoundLe GF (2 ^ 29)]`, pre `+ threadTok` |
| `examples/axiomcx/bboltnan/Run.lean` | the section's `variable [ThreadBoundLe GF (2 ^ 29)]` |

**Exported: none.** `mergedCreate_window`'s statement is unchanged (it reads the instance off `isServerM`'s
`threadBound GF ≤ rdPoolN`); `SnapApplyWalk` does the same before `OpenSnapshotBackend`; the three
`applyAll` proofs unfold `srvGoRes` around `createMergedSnapshotMessage` for its token.

Token flow as in §2: `wp_fork_tok_self` at `unsafeCommit`'s rollback goroutine (the fresh token to the
new read transaction, or to the post at the stop), at `newBackend`'s `go b.run()` and at
`newSnapshotReaderCloser`'s goroutine.

**Re-attack** (`f37d8ce925`, `examples/axiomcx/bboltrd`, cherry-picked on a scratch copy of `begin-tok`,
not committed): `Run.lean` no longer builds. `Run.lean:88`: `failed to synthesize ThreadBoundLe GF (2 ^ 29)`
at `Open_kv`. With the instance supplied as a section variable, the read `Begin_kv`s fail
(`Run.lean:106`, the first `Begin(false)`, and `:126`, the loop's), both with the unsolved goal `threadTok`. The
counterexample took `2 ^ 30` read transactions from one goroutine, so it would need `2 ^ 30` thread tokens,
and the instance bounds them below `2 ^ 29`.

**Gate** `etc/reader-slot-check.py` (in `etc/gates.sh`; pairs `etc/reader-slot-pairs.txt`, allow list
`etc/reader-slot-allow.txt`). It scans the Go sources, not the translations, so names-only functions such as
`backend.Snapshot` are scanned too. Calls are resolved by type, and a literal `bool` argument is specialised.
On `lean` `007725626e` (with this branch's script and lists) it FAILS, naming exactly `bbolt.DB.Begin_kv`
and `backend.backend.Snapshot`. On `begin-tok` it PASSES with 3 slot holders: `Begin_kv` and `Snapshot`
are paid and paired; `storage.OpenBackend` is allowed (paid by the run goroutine's fork token,
`notes/axiom-review/begin-tok-restated.md`, A9). The first, untyped version also flagged `Open_kv`,
`Tx.Commit_kv`, `newKVHasher` and `monitorKVHash`; all were name-resolution artifacts, cleared by the
typed resolution with no allow entries. Limits, stated in the docstring:
- 190 axioms are unscanned: 164 have no Go source here, 26 are variants with no Go function of that name
  (superseded by the fail-closed version: "Freeze conditions" below).
- The A10 hazard: a callback run inside `db.View`.

**Checks** (branch at `fca702da30`):
- Full build: 13384 jobs, no error.
- `etc/tcb-report.py --check`: 817 axioms, 4 `sorry`s, unchanged. Every `etc/tcb-collections/*.txt --check` passes.
- Interfaces regenerated for `etc/api/{backend,bbolt,etcdstart,raft}.txt`: only bbolt's and backend's changed (19 files against `lean` `2aff086a7f`): the five restated axioms, in their spec and proof files (bbolt `DB.Begin_kv`, `Open_kv`, `Tx.Rollback_kv`; backend `backend.Snapshot`, `snapshot.Close`), and the proof files of nine proved backend functions whose specs changed (the Internal table): `New`, `newBackend`, `newBatchTxBuffered`, `backend.begin`, `backend.unsafeBegin`, `backend.run`, `batchTxBuffered.commit`, `batchTxBuffered.unsafeCommit`, `batchTxBuffered.CommitAndStop`. No API module's interface changed.
- api-check and `--layout` pass for all four. bounds-check: 389, the baseline. errorf-wrap and errdesc pass. gen-init `--check` passes.
- Closed theorems (`*_safe`/`*_adequate`): 55 compared with `lean` `007725626e`, none differs. `srvBeSnapOk` occurs in no hub definition.

## Freeze conditions (2026-11-06)

The user approved the Freeze on condition of these fixes, made at `b8fc89f509` (gate script only; no
Lean changed, so the build at `94d520de7e` stands):

1. **Fail closed.** `etc/reader-slot-check.py` exits 1, naming the tree, when a Go source tree it needs is
   missing: `.lake/goose/bbolt` and `.lake/goose/etcd` always, and the project of every axiom's package
   (`PROJECTS`, per part: main raft is `raft`, RaftWitness's `raft-witness`, `github_com/mit_pdos/etcd_grove`
   this repository); also a missing package in such a tree, a package resolved to another tree than its
   project's (`bbolt-bank` standing in for `bbolt`, `raft-witness` for `raft`), a standard-library package
   absent from GOROOT, and a sourceless package not in the explicit `THIRD_PARTY` list. `go env GOROOT`
   failing exits 1 (`56ce2e5fd6`). A floor: `MIN_SCANNED = 200` (the docstring says to raise it to the
   printed count when axioms are added). Tested with `READER_SLOT_GOOSE` pointing at a scratch directory of
   symlinks to all trees but one (`.lake/goose` untouched): without `bbolt` exit 1 (`Go source tree
   .../bbolt is missing or has no go.mod (always needed ...)`, then each bbolt axiom "found in
   .../bbolt-bank, not in project bbolt"); without `etcd` exit 1; without `raft` exit 1 (4 errors: the
   tree, and 3 axioms resolved to `raft-witness`); without `raft-witness` exit 1 (3 errors); an empty
   directory exit 1 (all four trees named); without `go` on PATH exit 1; a copy with the floor at 201
   exit 1 (`200 axioms scanned, below the floor`); a copy whose token pattern matches nothing fails on
   exactly `bbolt.DB.Begin_kv` and `backend.backend.Snapshot`.
2. **Duplicate axiom names.** Every file is now checked, each tree against its own sources (RaftWitness's
   raft against `raft-witness`; the package cache and struct table are per tree). Before: 400 axiom
   lines matched, 13 duplicate names silently dropped (RaftWitness's copies of `DescribeConfChange`,
   `raftpb.ConfChangeType.String`, `strconv.FormatUint` and 9 `proto.*`, and `k8s.io/api/apps/v1`'s
   `Resource`), and `zap.Int'` missed by the name pattern: 387 checked, 197 scanned, 190 unscanned. After:
   401 axioms in 401 files, 200 scanned (the 3 RaftWitness raft/strconv copies added), 201 unscanned (175
   third-party, 26 variants with no Go function of the name). Still 3 holders, all paid and paired or
   allowed; the gate passes, also as `etc/gates.sh` runs it (its PATH, `GOTOOLCHAIN=go1.27.1`).
3. **Rechecks at `56ce2e5fd6`/`b8fc89f509`** (lean `2aff086a7f` merged):
   - Closed theorems: every `*_safe`/`*_adequate` statement compared with `lean` `2aff086a7f` by
     source text (the Draft's method): 55 compared, 0 differ; no changed `.lean` file declares one, and in
     `.lake/tcb.json` (at `94d520de7e`) `srvBeSnapOk` is in the statement definitions only of the linked
     `EtcdServer.wp_createMergedSnapshotMessage`, of no closed theorem.
   - `etc/gen-interface.py etc/api/<pkg>.txt --check` for backend, bbolt, etcdstart, raft: all pass;
     `--layout`: 0 new violations each. `etc/api-check.py --check`: all four pass (the warnings are
     `lean`'s). The changed interfaces against `lean` are those listed under Checks above (corrected).

## Follow-ups (after landing)

Weaknesses of the reader-slot gate, recorded for later, not fixed in this stage:

- (a) The token test is a regular expression over the whole spec file (comments stripped): a token
  mentioned anywhere in the file, not necessarily in the precondition of the holding triple, passes.
- (b) An allow entry (`etc/reader-slot-allow.txt`) is matched by the axiom's name only; it should also
  name the lock it covers and the pairing it relies on, and the check should match both.
- (c) The release heuristic: when a holder's result is not bound to a variable, any later resolved call
  of a releaser of the same lock in the caller clears it, whether or not it releases that slot.
- (d) A lock's identity is (package, field name): two `RWMutex` fields of the same name in one package
  are one lock to the check.
