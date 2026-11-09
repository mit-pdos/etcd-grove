/-
# bbolt's commit path: internal vocabulary (batch 4c)

Not part of the client API: the stages of a write transaction's `Commit`, for the internal specs
that mirror it (`Bucket__rebalance`, `Bucket__spill`, `Tx__commitFreelist`, `Tx__write`,
`Tx__writeMeta`). Their realization is the proof's invariant design (the old `bbolt-inv/design.md`:
the node cache's abstraction relation, the pages a transaction allocated, the writer's share of the
file under `rwlock`); this module only names the stages so that `Tx.Commit.spec`'s sketch has
specs to apply.

* `wtxAt tx γ T st` (exclusive): the write transaction `tx` (all of it, `rwlock` held), whose data is
  `T.cur`, has reached the commit stage `st`:
  - `nodes`: rebalanced (no node below its minimum fill, no empty non-root page, no root branch of
    one child);
  - `spilled`: every dirty node written to freshly allocated in-memory pages (`tx.pages`), split to
    fit, the parents' keys exact, the root page set in `tx.meta`, the old pages freed as pending
    for this txid (batch 4d's `freelist.Free`), and (without `NoFreelistSync`) the freelist page
    written; `tx.meta`'s high-water mark covers every allocated page;
  - `flushed`: those pages in the file (`pwrite`, `fdatasync` unless `NoSync`), none of them
    reachable from the current meta; the file at least `hwm · pageSize` long.
* Each stage still lets the writer roll back (`Tx.rollback`: 4d's `freelist.Rollback`, then
  `NoSyncReload` of `freepages` or `Reload` of the synced freelist page) to `txDone tx`, the
  committed state untouched.
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

/-- (internal) The stages of a write transaction's commit (see the header). -/
inductive CommitStage where
  | nodes
  | spilled
  | flushed

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- (internal) The write transaction `tx`, at view `T`, at the commit stage `st` (exclusive). -/
opaque wtxAt [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName)
    (T : TxView) (st : CommitStage) : IProp GF := iprop(True)

end vocab

end Bbolt
end EtcdGrove
end Perennial
