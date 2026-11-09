/-
## `Interface.Rollback(txid)` (`shared.go`)

**Users.** tx.go:318 (`nonPhysicalRollback`), tx.go:336 (`rollback`, then `NoSyncReload`/`Reload`). Snippet `ReqRollback`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; per pending id of `txid`: out of `cache`, its allocating transaction back in `allocs` (the panic: `canRollback`); the entry deleted; `txid`'s `allocs` deleted. An early return when `txid` freed nothing.
**Changes.** from `specs-ref`'s `Interface__Rollback.lean`: over `FLState`; the panic as the premise `canRollback`.
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Freelist

open Iris Iris.BI go_etcd_io.bbolt.internal.common BboltCommon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.Rollback(txid)`: undoes `txid`'s frees and forgets its allocations (`FLState.rollback`; nothing if it freed nothing). It panics if `txid` freed a page it allocated: `canRollback` excludes it. -/
def Interface.Rollback.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (txid : Txid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ ⌜F.canRollback txid⌝ }}
    (App (flCall fl go!"Rollback") (Val #txid))
  {{ RET #(); flOwn fl (F.rollback txid) }}

end spec

end Freelist
end EtcdGrove
end Perennial
