/-
## `Interface.NoSyncReload(ids)` (`shared.go`)

**Users.** tx.go:343 (`rollback` without a synced freelist: `db.freepages()`, the pages no committed tree reaches); `Reload` (internal). Snippet `ReqRollback`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; a map of the pending ids, the ids filtered into a new slice, `Init` (sorted, so the hash map's check passes).
**Changes.** from `specs-ref`'s `Interface__NoSyncReload.lean`: over `FLState`; the slice is only read; the old premise for the hash map kept (round 1, F1).
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

/-- The contract of `NoSyncReload` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.NoSyncReload(ids)`: the free pages are `ids` (strictly increasing, from 2 on) but the pending ones; `ids` is only read. The hash map's `Init` returns before its reindex when the new ids are empty, so its `cache` would keep the old free ids (`Freed` true, `Free` panicking): the premise (the ids left after the pending ones are dropped are not empty, or no page was free) excludes it (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). -/
def Interface.NoSyncReload.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (s : GoSlice) (ids : List Pgid) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ s ↦*{dq} ids ∗
      ⌜idsOk ids ∧ (ids.filter (fun x => decide (x ∉ F.pending)) ≠ [] ∨ F.free = GMap.empty)⌝ }}
    (App f (Val #s))
  {{ RET #(); flOwn fl (F.reload ids) ∗ s ↦*{dq} ids }}

/-- `f.NoSyncReload(ids)`: the free pages are `ids` (strictly increasing, from 2 on) but the pending ones; `ids` is only read. The hash map's `Init` returns before its reindex when the new ids are empty, so its `cache` would keep the old free ids (`Freed` true, `Free` panicking): the premise (the ids left after the pending ones are dropped are not empty, or no page was free) excludes it (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). Through the interface (`flCall`): proved from `array.NoSyncReload.spec`, `hashMap.NoSyncReload.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.NoSyncReload.spec : Prop := ∀ fl, Interface.NoSyncReload.contract (GF := GF) fl (flCall fl go!"NoSyncReload")

end spec

end Freelist
end EtcdGrove
end Perennial
