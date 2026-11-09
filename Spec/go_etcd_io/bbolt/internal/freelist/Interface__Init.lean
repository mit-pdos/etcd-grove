/-
## `Interface.Init(ids)` (`array.go`, `hashmap.go`)

**Users.** db.go:457 (`loadFreelist`: `fl.Init(db.freepages())`, the pages no tree reaches, on a database without a synced freelist); `Read`, `NoSyncReload` (internal).
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; the array keeps the slice (`f.ids = ids`) and reindexes; the hash map checks `sort.SliceIsSorted` (trusted, `req/sort.md`), builds maximal spans and reindexes.
**Changes.** from `specs-ref`'s `Interface__Init.lean`: from any state, not only the empty one (`Reload` reinitializes a live freelist); the new free pages must not be pending (`flOwn_wf`).
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

/-- `f.Init(ids)`: the free pages are `ids` (strictly increasing, from 2 on, none pending: the hash map panics on unsorted ids); the array keeps the slice, so it is consumed. -/
def Interface.Init.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (s : GoSlice) (ids : List Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ s ↦* ids ∗ ownSliceCap Pgid s (DFrac.own 1) ∗
      ⌜idsOk ids ∧ ∀ x ∈ ids, x ∉ F.pending⌝ }}
    (App (flCall fl go!"Init") (Val #s))
  {{ RET #(); flOwn fl (F.init ids) }}

end spec

end Freelist
end EtcdGrove
end Perennial
