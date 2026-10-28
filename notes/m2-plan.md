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
