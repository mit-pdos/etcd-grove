# Plan: M2, compaction in the server's model (spec-first)

Status: phase 0 decided (2026-10-27, the user's: decisions 1(a), 2 and the reader redefined in
place; 3 and 4 as drafted). Next: phase 1, the spec skeleton. The compactor pilot's
server side (`notes/compactor-pilot-plan.md`, "The server side" and "The scope narrowed"), run as its
own spec-first stage (`notes/spec-first-plan.md`). It is also the first test of the pilot's freeze:
the compactor's frozen specs (`v3compactor`) must not change.

## What exists (the survey, 2026-10-27)

- **mvcc's compaction-aware path is complete**: `storeReaderC`, `store.Read` with a compaction lower
  bound, `rangeOutcomeC` (`ErrCompacted` exactly below the observed compaction revision, else the
  full log), `store.Compact.spec` (`compactRight`, `crevLb`, `NoDelPutAt`), and the laws
  `storeReader_toC : storeReader ⊢ storeReaderC ∗ crevFrozen`, `storeReader_of` (`mvcc/InvStore.lean`
  3328-3360). Nothing above mvcc uses it: every package takes the frozen corollaries (`storeReader`
  carries `crevFrozen`, the store never compacted; `NewServer` allocates it, `crevFrozen_alloc`).
  Missing: an **upper** bound on the compaction revision a reader can see (only lower bounds exist).
- **The examples' theorems** (`putget_safe`, `watch_safe`, `cache_safe`, ...) state no panic and no
  stuck thread; none mentions compaction. They are about a Go program whose compactor is off
  (`examples/common/common.go`: `AutoCompactionRetention` zero, a `NewServer` premise).
- **`ErrCompacted` as an answer**: a range's error case and the client's `kv.Get` error case are
  unconstrained, so an `ErrCompacted` read already fits as a failed operation; a successful read is
  still answered from the full log (M2's point: compaction drops no value at a revision it keeps).
- **What changes** (56 of the 66 `storeReader` files are mvcc's; 10 are the cache's own name):
  - pass-through only (about 21: mvcc's write side, lease, apply, v3rpc, client, examples' glue): no
    change if `storeReader` keeps its name and is redefined (below);
  - real statement changes (about 12, plus `rangeEvents`, `store.Restore`, `watchableStore.Restore`):
    txn's `Range`/`Txn`/`Count`/`checkRange`/`checkTxn` and `isTxnRead`'s "never compacted" defaults
    (17 more txn files use them), the watchable store (its invariant has `compacted = false`,
    `chooseAll` excludes the compaction branch, `watcher.send` fixes `CompactRevision = 0`), v3rpc's
    and the client's `compactRev = 0`, `RestorePre`/`SnapApplyDefs`, `NewServer`.
- **`NoDelPutAt`**: `store.Compact` needs no delete-then-put of a key within one revision, which a
  plain transaction can violate (`issues/etcd-compaction-delete-then-put.md`, etcd-io/etcd#22377). A
  workload of single puts meets it trivially.

## Phase 0: the decisions (the user's, 2026-10-27)

1. **The program.** (a) A new example, `putgetc`: `putget` with the auto-compactor on, leaving every
   existing example and theorem as is; or (b) turn the compactor on in `examples/common`, changing
   every example's program at once. **Taken: (a).**
2. **The configuration of the first result.** One member; the auto-compactor in **revision mode**
   (no clock trust boundary: the pilot's `revPermit`), a fixed retention; puts and latest gets only;
   no watches, no client `Compact`, no snapshot restore. Widening (periodic mode, watches from old
   revisions, client compactions, `Restore`) is a later stage each. **Taken.**
3. **`NoDelPutAt`**: met by the workload in (2) (single puts), kept as a premise of the apply's
   compaction arm, citing the issue; the fork fix later if a workload needs transactions.
4. **The top-level statement**: `putgetc_safe`, the same shape as `putget_safe` (no panic, no stuck
   thread) for the program in (1); and, as library results, `applyEntries_model` without the
   "neither a compaction" premise, and reads that may answer `ErrCompacted` only at a revision at or
   below `compactLb`, where `compactLb` is at most what the compactor's permit allows (C3).

## The trusted statements M2 changes (to approve with phase 1's drafts)

`NewServer.spec`/`specOn` (the `AutoCompactionRetention = 0` premise goes); `apply.dispatchOk` and the
three apply specs over it; `plainCover`, `putgetKind`, `plainReq`, `logShape`'s "neither a
compaction"; `reqPropOk`/`reqPropOkM` (a compaction form carrying the C1 permit); `storeReader`'s
definition (**taken**, the user's: keep the name, redefine as `storeReaderC` plus an invariant tying the
compaction revision to a new server-wide `compactLb`, replacing the frozen `-1`) and txn's defaults;
`checkRangeErr` and txn's `Range`/`Txn`/`Count` results; `rangeEvents`, `store.Restore`,
`watchableStore.Restore` (unless (2)'s exclusions keep them on the frozen path). Unchanged: the
client's KV specs, v3rpc's KV results (beyond the reader), the cache's results, every existing
example theorem.

## Open (for phase 1)

- Whether the watchable store can stay on the frozen path while watches are out of scope (a second
  reader kind), or must be generalized now because `storeReader` is shared.
- Whether `Restore` is unreachable for one member (then it keeps its premise).
- Whether the client's error predicate admits gRPC's compacted status (the read path's error answer).

## Phase 1: the design of the skeleton (2026-10-27)

**The reader, redefined** (phase 0's decision): `storeReader s γ` loses `crevFrozen` and becomes
`storeReaderC` plus what a read needs of the compaction revision `c` it observes. What a read needs
depends on the result:
- **For `putgetc` (latest reads only), nothing tied to the compactor.** mvcc's `rangeOutcomeC`
  answers `ErrCompacted` exactly when the revision read at is below `c`
  (`mvcc/InvStore.lean`, `rangeOutcomeC`); a latest read is at the store's current revision, and
  `c` never exceeds it (a compaction's revision is one of the committed log, `store.Compact`'s
  premise). So the reader's statements change from "`c = -1`" (the frozen corollaries, the
  transactions' `crev := -1` defaults) to "`c` the observed revision, `c ≤` the transaction's
  revision", and a latest read's outcome is still `rangeOutcome` (a lemma like
  `rangeOutcomeC_neg`, for `c ≤ rev`).
- **For C3 (phase 0's library result: `ErrCompacted` only at or below a server-wide `compactLb`,
  itself at most what the compactor's permit allows), an mvcc change.** A reader learns `c` only
  as a lower bound (`crevLb`); bounding it from above needs a share of the revision's authority in a
  server invariant beside `compactLb`. The authority is split between the store's lock invariant
  and `compactRight` (half each), and `store.Compact` takes the right's whole half for the call
  (non-atomic), so no invariant can keep a share. The general fix is mvcc's: `store.Compact` with
  a logically atomic update at its linearization point (`updateCompactRev`, under `s.mu`; TaDa
  style, the caller's invariant over a share of the right); a respecification of a proved mvcc
  function (`store.Compact` 157 proof lines, `store.updateCompactRev` 341) and its one caller
  (the apply's compaction arm).

**The stages** (phase 0's S1-S4, refined):
- **S0, the program**: `examples/putgetc` (Go: `putget` with `AutoCompactionMode: "revision"` and a
  fixed retention; `examples/common` gains the configuration as a parameter of `newServer`, zero
  for every existing caller), its Goose project, and `putgetc_safe`'s statement over it.
- **S1, the readers**: `storeReader`'s new definition; txn's read specs (`Range`, `Txn`, `Count`,
  `checkRange`, `checkTxn`, `isTxnRead`'s default) over the observed `c`; `rangeEvents`,
  `store.Restore`, `watchableStore.Restore`, the watchable store's `compacted = false` (kept on the
  watch path as a premise while watches are out of scope, if the shared reader allows it: open).
- **S2, the apply's compaction arm**: `apply.dispatchOk` without the compaction conjunct; the arm's
  spec over `store.Compact` (`compactRight` held by the apply thread, `NoDelPutAt` from the
  workload); `reqPropOk`'s compaction form carrying `revPermit`; `applyEntries_model` without
  "neither a compaction".
- **S3, `EtcdServer.Compact`'s glue** over `processInternalRaftRequestOnce` (the pilot's last
  `sorry`), against the frozen compactor specs (the freeze's test).
- **S4, `NewServer` with the compactor on**: the `AutoCompactionRetention = 0` premise replaced by
  revision mode's; `crevFrozen_alloc` replaced by the apply thread's `compactRight`; then
  `putgetc`'s `Main` and `putgetc_safe`.
- **S4's contract** (designed 2026-10-27): the server's `compactorOk c` (`etcdserver/InvRun.lean`,
  persistent, nil until now) becomes `c = nil ∨ ∃ T P, v3compactor.compactorOk c T P` (what `run`
  uses: `Pause`/`Resume`, persistent triples), and a new one-shot `compactorRun c` in what `start`
  takes (`c = nil ∨` the run token and `runPre E (revPermit E.RevLb ret)`), spent by `start`'s
  `s.compactor.Run()`. `NewServer` builds both from the frozen `v3compactor.New.spec`: `E.rg` the
  store (`srv.kv`, mvcc's `Rev`), `E.c` the server (`EtcdServer.Compact.spec`, S3: a callee
  hypothesis of `NewServer`'s proof, which builds the closure without calling it), `E.R` a store
  reader of the 64, `E.RevLb` mvcc's revision lower bound. The compactor's specs are used as
  frozen (the freeze's test).
- **S5 (only with C3)**: mvcc's atomic `store.Compact`, `compactLb`, and the bound's statement.

**C3 deferred** (the user's, 2026-10-27): the first result is `putgetc_safe`, with reads answering
`ErrCompacted` exactly below the observed compaction revision (mvcc's statement); C3 and S5 are a
later stage. A scope revision of phase 0 (decision 4), found in phase 1's design, before any spec.

## Phase 1, S0: the program and the top-level statement (2026-10-27)

- **Go**: `examples/putgetc` (putget with `common.StartCompactingServer(..., retention = 1, ...)`:
  revision mode, the most aggressive retention, every compaction at the revision before the
  store's); `examples/common`'s `newServer` takes the retention (`AutoCompactionMode: "revision"`,
  `AutoCompactionRetention: time.Duration(retention)`), zero from every existing caller. Its Go
  test passes; Goose project `putgetc`; `gen-init.py` roots and package table.
- **Statements**: `putgetc.Main.spec` and the closed `putgetc_safe` (putget's, at putgetc's
  addresses and name: `Proof/.../examples/putgetc/`), `common.StartCompactingServer.spec`
  (`StartServer`'s, `0 < retention`), `common.newServer.spec` with the retention (`= 0`) and its
  compacting variant `newServer.specCompact` (`0 < retention`).
- **The one gap**: `newServer.wp_proofCompact` (`sorry`: S4's `NewServer` with the compactor).
  **Why a variant, not one spec with `0 ≤ retention`**: Lean tracks axioms per declaration, so one
  proof with a `sorry` in its compactor-on case would put the `sorry` under `putget_safe` and every
  example built on `newServer`. The variant keeps it under `putgetc` alone
  (`etc/tcb-collections/m2.txt`); S4 merges the two. The same applies to every generalized
  statement of S1-S4: a generalization's unproved case goes in a variant, linked by hand
  (`putgetc/MainLinked.lean`), until it is proved.

## Phase 1, S1: the readers' statements, drafted (2026-10-27; for the user's approval)

**What uses the frozen store today** (measured): mvcc's frozen layer (`FrozenSpecs.lean`: 14 specs
restated at compaction revision `-1`, `<fn>.specFrozen`, with corollaries `<fn>.spec_frozen`), used
by 31 mvcc proofs and 14 above mvcc (txn 8, apply 1, v3rpc 1, etcdserver 4); the `crevFrozen`
fact itself in the watchable store (`syncWatchers`, `newWatchableStore`, `rangeEvents`,
`InvCompact`, `InvRoTxn`), `store.Restore`/`watchableStore.Restore`, `NewStore`, and the server's
restore (`RestorePre`, `SnapApplyDefs`) and allocation (`Results`). The watchable store must be
generalized even with watches out of scope: its `syncWatchers` goroutine runs in every server,
`putgetc`'s too, and its invariant assumes no compaction.

**The drafts:**
1. **`mvcc.storeReader s γ := storeReaderC s γ`** (the frozen fact dropped; the name kept, phase 0's
   decision). `crevFrozen`, `crevFrozen_alloc` and the frozen layer go; `NewServer` keeps the
   compaction right (`compactRight γ (-1)`) for the apply thread instead of freezing it.
2. **The frozen layer becomes the readers' layer** (`ReaderSpecs.lean`, `<fn>.specR`): each
   `specFrozen` with the observed compaction revision exposed instead of fixed at `-1`: the read
   transaction `isTxnRead mw s γ trace log rev crev True` (the tag `True`, as the general spec's
   compacting clients), `crevLb γ.idx crev`, `crev < log.length` (a compaction revision is one of
   the log's); a range's outcome `rangeOutcomeC … crev` (`ErrCompacted` exactly below `crev`)
   instead of `rangeOutcome`, with the lemma that a latest read (`ro.Rev = 0`) is never compacted
   (generalizing `rangeOutcomeC_neg`).
3. **txn**: `checkRangeErr rev crev o err`: `ErrCompacted` when `o.rev ≠ 0 ∧ o.rev ≤ rev ∧
   o.rev < crev` (was `< -1`); `txn.Range`/`Txn`/`Count`/`checkRange`/`checkTxn`'s posts gain
   `∃ crev, crevLb γ.idx crev ∗ ⌜crev ≤ rev⌝` and their results are over it (`rangeResult … crev`);
   `Range`'s never-done clause gains the compacted case. `Put`/`DeleteRange` only read at the
   current revision: unchanged.
4. **The watchable store**: its invariant drops `st.compacted = false`; `chooseAll`/`choose` lose the
   premise excluding their compaction branch; `watcher.send`'s `CompactRevision = 0` becomes the
   compaction revision's value when the store compacted the watcher; `rangeEvents`' snapshot misses
   no event above the compaction revision; `syncWatchers` over the observed revision.
5. **Restore**: `store.Restore`/`watchableStore.Restore` from the compaction right at its current
   revision (was: frozen at `-1`); `RestorePre`/`SnapApplyDefs` carry the right, not the frozen fact.
6. **Above txn** (apply, the server's `Range`/`Txn`, v3rpc, the client): the range's error case is
   already unconstrained (survey), so only the reader's name and the `specR` corollaries change.

What the user approves here: (1)'s definition and (3)-(5)'s statements (trusted: they are the
statements of linked results, e.g. `txn.Range`'s).

## Phase 1, S2-S4: the statements, drafted (2026-10-28)

**Redirected (the user's, 2026-10-28): the skeleton before the proofs.** S1's re-proofs stop at
its statements (the proofs that are more than threading become `sorry`s); S2-S4's statements are
drafted and their glue proved; a `spec-reviewer` round runs on the whole skeleton; only then the
proofs. (S1 had gone to re-proving about 45 files before S2-S4 existed: the old order.)

**S2, the apply's compaction arm.**
- `apply.dispatchOk on rq` loses `dispatchKind rq ≠ .compaction` (`apply/InvUber.lean`).
- `dispatchStep` needs no change: compaction is not a `storeKind`, so the log is unchanged
  (`o.logAfter log = log`), which is true (a compaction changes no value at a revision it keeps).
- The arm's spec (`applierV3backend.Compaction`, over `store.Compact`): the apply thread holds the
  compaction right (`compactRight γ c`, given by `NewServer` instead of frozen) and passes it
  through; a request at `r ≤ c` answers `ErrCompacted`, above the log `ErrFutureRev`.
- `reqPropOk` gains a compaction form: `⌜dispatchKind rq = .compaction ∧ ¬ physical rq⌝` with a
  trivial result (`Qr = True`). No permit: C3 is deferred, and a latest read is never compacted
  whatever the revision (so `EtcdServer.Compact.spec`'s "any revision" stays).
- `applyEntries_model`'s "neither a compaction" premise goes.
- **Open: the delete-then-put premise** (`store.Compact` needs `NoDelPutAt log r`,
  `issues/etcd-compaction-delete-then-put.md`). The server's specs are generic in their clients
  (any gRPC client can send `Then(OpDelete(k, WithFromKey()), OpPut(k, v))`), so the workload
  cannot discharge it at the apply. Choices:
  (a) a premise on the admitted writes, in compaction mode only: the server's request forms
      (`reqPropOk`'s write forms, through `isServerReqM`'s mode) exclude a transaction that
      deletes and puts one key; it reaches the clients' `Txn` specs only when the compactor is
      on (`putgetc` issues none), citing the issue;
  (b) fix the Go: upstream's PRs (etcd-io/etcd#22377, `keyIndex.doCompact`; #22395, the gRPC
      path) in the fork, so `store.Compact` needs no premise; re-proves mvcc's `doCompact` and
      `store.Compact` (proved, about 500 lines with `updateCompactRev`).
  (a) is phase 0's scope (decision 3) made precise; (b) removes the premise for every later
  widening. **Taken: (a)** (the user's, 2026-10-28).

**S3, `EtcdServer.Compact`'s glue** over `processInternalRaftRequestOnce` with `reqPropOk`'s
compaction form; its statement unchanged (the pilot's). Checked while drafting: its `idCred` is
persistent (the time-receipt bound), so the compactor's `R` can hold it across calls.

**S4, the server with the compactor.**
- `NewServer.spec`/`specOn`: `AutoCompactionRetention = 0` becomes `retention = 0 ∨ (mode =
  "revision" ∧ 0 < retention)` (phase 0's scope).
- The server's `compactorOk c` (`InvRun.lean`): `⌜c = nil⌝ ∨ ∃ T P, v3compactor.compactorOk c T P`
  (persistent: `run`'s `Pause`/`Resume`); new `compactorRun c` in `start`'s resources: `⌜c = nil⌝ ∨
  ∃ T, v3compactor.compactorOk c T (runPre E (revPermit E.RevLb ret)) ∗ T ∗ runPre …`, spent by
  `s.compactor.Run()`.
- `E` (the compactor's environment, built by `NewServer`): `E.rg` the store (`s.kv`, its `Rev` over
  `storeReader`), `E.c` the server (`EtcdServer.Compact.spec`), `E.R := srvLeadTimeReader s ∗ E.RD ∗
  storeReaderC ∗ ownToks γ.revs m` (all given back by both calls) with `□ idCred`, `E.RevLb n := ∃
  log, idxCert log ∗ ⌜n ≤ log.length - 1⌝`.
- `newServer.specCompact` merges into `newServer.spec` (`0 ≤ retention`).

**The glue to prove before the review**: `newServer` (both cases), `start`'s `Run` call, `run`'s
`Pause`/`Resume` calls, `NewServer`'s construction of `E` and the `New` call (the compactor case),
`EtcdServer.Compact`, `putgetc.Main` (done).

## Phase 1, S1 steps 4-5: two scope revisions (2026-10-28, the user's)

Writing the statements of drafts 4 and 5 found both understated (phase 1, before any review or
proof):
- **The watchable store** (draft 4): stating its compaction case needs the watch response model
  (`RespM`, `mvcc/InvWatchStore.lean`, in 173 files) to carry a compaction revision, and every
  consumer (v3rpc's watch stream, the client's watch proofs, the cache, the examples' watch models)
  to drop `compactRev = 0`: a watch stage of its own. **Taken: no watchers in compaction mode.** The
  watchable store's invariant admits a compacted store only while no watcher is registered (phase
  0's "no watches"), so `syncWatchers`' compaction case is vacuous and `RespM` is unchanged; the
  watch stage is a later widening.
- **Restore** (draft 5): `store.Restore` installs a backend never compacted (the compaction
  revision back to `-1`), while the compaction right is a monotone counter: a restore needs the
  compaction ghost state redesigned (the D22 snapshot track, the collaborator's). **Taken: no
  restore in compaction mode.** Only the server configuration that never installs a snapshot (one
  member, D21 M3's no-snapshot bound) gets the compactor; `Restore` keeps its frozen premise for
  compaction-off servers.
Counted as the stage's phase-1 scope revisions (found by drafting, not by proof).

## Phase 1, S2-S4: the fork's result, and the freeze test (2026-10-28)

Committed: `0e344652a6` (S4 statements and glue: the server's `compactorOk` split into the
persistent contract and a one-shot `compactorRun`, spent by `start`'s `Run`; `run`'s
`Pause`/`Resume`; `newServer.wp_proofCompact` over `NewServer.specCompact`), `872a204cd7` (S2
statements: `CompactMode.lean`, `reqPropOkC`, `dispatchOkC`, `irrNoDelPut`,
`processInternalRaftRequestOnce.specCompact`). The mode is a variant per statement (as auth's
`specOn`); compaction-off statements and proofs unchanged. Open `sorry`s (new cases):
`NewServer.wp_proofCompact` (the compactor's environment, the apply thread's compaction right),
`processInternalRaftRequestOnce.wp_proofCompact` (the apply's compaction arm), `Compact.wp_proof`,
and S1's `syncWatchers` (2) and `RestorePre` (1).

**The freeze test failed: one revision after the freeze.** `EtcdServer.Compact` (`v3_server.go`)
calls `traceutil.EnsureTrace(ctx, …)`, which reads `ctx.Value(TraceKey{})` and, if it finds a
trace, writes to it; the frozen `v3compactor.compactableOk` and the pilot's `Compact.spec` give
the call only `context.isContext ctx cd`, which says nothing of `Value` for other keys, so
`Compact.spec` is unprovable. Cause: CALLER (a need of the callee's body, found by S3's glue).
The criterion that should have caught it: "a contract with no resource over a callee that needs
one" -- the reviews checked `compactableOk` against `Compact.spec`, itself an unproved `sorry`,
not against `Compact`'s Go body. **Repair (the user's): the context carries no trace.**
`compactableOk`'s per-call premise and `Compact.spec` gain `traceutil.ctxTraceIs ctx none`;
`Run` proves it for its `WithCancel(Background())` from `ctxTraceIs_background` and a law that
`WithCancel` passes `Value` to its parent for other keys (missing in Perennial:
`notes/perennial-changes.md`; meanwhile a local lemma over Perennial's context, a justified unfold
like `isContextDef`'s).

**Findings for the review** (the fork's): the compaction mode is not enforced by the statements
(`NewServer.specCompact`'s post still hands out the 64 watch readers; the request path's variant
takes a plain `isServerReq`); `Compact`'s callee hypotheses lack `Trace.AddField`; the callee-free
`NewServer.wp_proofCompact` stub hides `NewServer`'s axioms from the `m2` collection's baseline (not
updated).

## After review round 1: one family, the Go bug fixed (2026-10-28, the user's)

Round 1 (`notes/spec-first-study/m2-review-1.md`) found the compaction mode in no statement; the
repair (`8950d80bf2`: `isServerReqC`, `kvInvC`, `CompactEnv.lean`'s `compactableOk_server`) showed
that enforcing it means a compaction-mode family through the whole serving stack (the request
path's `Put`/`Range`/`Txn`/`DeleteRange`, v3rpc, the client, `common`), beside the off family:
against the rule "no special-case spec family beside the general one" (`LESSONS.md`). **Taken:
one family.** The delete-then-put decision changes from (a) to (b): upstream's fix
(etcd-io/etcd#22377, `keyIndex.doCompact`; #22395, the gRPC path) in the fork, mvcc's
`doCompact`/`store.Compact` re-proved without `NoDelPutAt`, the etcd pin bumped. Then one KV
invariant admits compaction entries for every server (no write restriction), `dispatchOk` loses its
compaction conjunct, and the `…C` statements merge into the general ones. Restore is excluded by a
`NewServer` configuration premise (compactor on only in the no-snapshot configuration); watchers by
a persistent "no compactor" fact that off servers hand out and the watch API takes. A phase-1
design revision found by review round 1 (decision 3 of phase 0 reversed).
