/-
`tx.rollback()` (`tx.go`): a writer's freelist rolled back (unless its meta is already current: kept) and reloaded, then `close`. Users: `Commit`'s error paths (`spill`, `commitFreelist`, `grow`, `write`,
`writeMeta`); `Rollback` calls `nonPhysicalRollback` instead (no reload).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). If the mapping is there and the current meta's txid is the
writer's (its meta page was written: the commit kept), `close` only: the pages it freed stay
pending. Else 4d's `Interface.Rollback` (`canRollback` from `wtxAt`'s invariant: every pending
entry this txid made has `alloc ≠ txid`, by `Free`'s `canFree`), then, with the mapping, a reload
of the free pages: no synced freelist, `NoSyncReload(freepages())` (`DB.freepages.spec`: `idsOk`,
`dbUnreached`); else `Reload(db.page(db.meta().Freelist()))` (the file's synced-freelist clause:
readable, distinct, from 2, below the high-water mark). 4d's F1 premise of both
(`req/go_etcd_io_bbolt_internal_freelist.md`, "from 4d"): the invariant 4c keeps (`Internal.lean`,
"The freelist's side") that **every free page is among the current meta's freelist ids, or among
the pages its tree does not reach, and not pending**; `Rollback` changes no free page, and the
current meta is the writer's base; so the reload's ids, the pending ones dropped, include every
free page, and are empty only if none is. After the reload the invariant holds again
(`FLState.reload`: free = those ids but the pending). Then `close`.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the transaction done. -/
def Tx.rollback.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (st : CommitStage),
  {{ wtxAt (GF := GF) tx γ T st }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"rollback")) (Val #()))
  {{ RET #(); txDone tx }}

end spec

end Bbolt
end EtcdGrove
end Perennial
