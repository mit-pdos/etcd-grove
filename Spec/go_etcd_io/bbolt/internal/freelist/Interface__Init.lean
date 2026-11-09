/-
## `Interface.Init(ids)` (`array.go`, `hashmap.go`)

**Users.** db.go:457 (`loadFreelist`: `fl.Init(db.freepages())`, the pages no tree reaches, on a database without a synced freelist); `Read`, `NoSyncReload` (internal).
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; the array keeps the slice (`f.ids = ids`) and reindexes; the hash map checks `sort.SliceIsSorted` (trusted, `req/sort.md`), builds maximal spans and reindexes.
**Changes.** from `specs-ref`'s `Interface__Init.lean`: from any state, not only the empty one (`Reload` reinitializes a live freelist); the new free pages must not be pending (`flOwn_wf`); the old premise for the hash map's early return kept (round 1, F1).
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

/-- The contract of `Init` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Init(ids)`: the free pages are `ids` (strictly increasing, from 2 on, none pending: the hash map panics on unsorted ids); the array keeps the slice, so it is consumed. The hash map's `Init` returns before its reindex when the new ids are empty, so its `cache` would keep the old free ids (`Freed` true, `Free` panicking): the premise (the new free pages are not empty, or no page was free) excludes it (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). -/
def Interface.Init.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (s : GoSlice) (ids : List Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ s ↦* ids ∗ ownSliceCap Pgid s (DFrac.own 1) ∗
      ⌜idsOk ids ∧ (∀ x ∈ ids, x ∉ F.pending) ∧ (ids ≠ [] ∨ F.free = GMap.empty)⌝ }}
    (App f (Val #s))
  {{ RET #(); flOwn fl (F.init ids) }}

/-- `f.Init(ids)`: the free pages are `ids` (strictly increasing, from 2 on, none pending: the hash map panics on unsorted ids); the array keeps the slice, so it is consumed. The hash map's `Init` returns before its reindex when the new ids are empty, so its `cache` would keep the old free ids (`Freed` true, `Free` panicking): the premise (the new free pages are not empty, or no page was free) excludes it (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). Through the interface (`flCall`): proved from `array.Init.spec`, `hashMap.Init.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Init.spec : Prop := ∀ fl, Interface.Init.contract (GF := GF) fl (flCall fl go!"Init")

end spec

end Freelist
end EtcdGrove
end Perennial
