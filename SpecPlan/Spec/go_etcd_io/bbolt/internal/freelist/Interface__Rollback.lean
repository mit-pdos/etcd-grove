/-
## `Interface.Rollback(txid)` (`shared.go`)

**Users.** tx.go:318 (`nonPhysicalRollback`), tx.go:336 (`rollback`, then `NoSyncReload`/`Reload`). Snippet `ReqRollback`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; per pending id of `txid`: out of `cache`, its allocating transaction back in `allocs` (the panic: `canRollback`); the entry deleted; `txid`'s `allocs` deleted. An early return when `txid` freed nothing.
**Changes.** from `specs-ref`'s `Interface__Rollback.lean`: over `FLState`; the panic as the premise `canRollback`.
**Margin.** none: the post is what the code computes.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.freelist.Api

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

/-- The contract of `Rollback` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Rollback(txid)`: undoes `txid`'s frees and forgets its allocations (`FLState.rollback`; nothing if it freed nothing). It panics if `txid` freed a page it allocated: `canRollback` excludes it. -/
def Interface.Rollback.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (txid : Txid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ ⌜F.canRollback txid⌝ }}
    (App f (Val #txid))
  {{ RET #(); flOwn fl (F.rollback txid) }}

/-- `f.Rollback(txid)`: undoes `txid`'s frees and forgets its allocations (`FLState.rollback`; nothing if it freed nothing). It panics if `txid` freed a page it allocated: `canRollback` excludes it. Through the interface (`flCall`): proved from `array.Rollback.spec`, `hashMap.Rollback.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Rollback.spec : Prop := ∀ fl, Interface.Rollback.contract (GF := GF) fl (flCall fl go!"Rollback")

end spec

end Freelist
end EtcdGrove
end Perennial
