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
