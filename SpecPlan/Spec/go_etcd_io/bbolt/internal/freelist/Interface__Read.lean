/-
## `Interface.Read(p)` (`shared.go`)

**Users.** db.go:460 (`loadFreelist`: the synced freelist page, into a new freelist); `Reload` (internal). Snippet `ReqWriteReload`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; `IsFreelistPage`, `FreelistPageIds` and `freelistIds_view` (`BboltCommon`), a copy, `sort.Sort` (the bound), `Init`.
**Changes.** from `specs-ref`'s `Interface__Read.lean`: from any state whose pending pages are not on the page (not only the empty one).
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

/-- The contract of `Read` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Read(p)`: the free pages are the freelist page's ids. It panics on a page of another kind or a count above `2^63` (`freelistReadable`); its ids must be distinct, from 2 on, and none pending (`Init`'s premise once sorted). The hash map's `Init` returns before its reindex when the new ids are empty, so its `cache` would keep the old free ids (`Freed` true, `Free` panicking): the premise (the new free pages are not empty, or no page was free) excludes it (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). -/
def Interface.Read.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ bytesPointsto p dq bs ∗
      ⌜freelistReadable bs ∧ (freelistIdsOf bs).Nodup ∧ (∀ x ∈ freelistIdsOf bs, 2 ≤ x.toNat) ∧
        (∀ x ∈ freelistIdsOf bs, x ∉ F.pending) ∧ (freelistIdsOf bs).length < flMaxIds ∧
        (freelistIdsOf bs ≠ [] ∨ F.free = GMap.empty)⌝ }}
    (App f (Val #p))
  {{ RET #(); flOwn fl (F.init (freelistIdsOf bs)) ∗ bytesPointsto p dq bs }}

/-- `f.Read(p)`: the free pages are the freelist page's ids. It panics on a page of another kind or a count above `2^63` (`freelistReadable`); its ids must be distinct, from 2 on, and none pending (`Init`'s premise once sorted). The hash map's `Init` returns before its reindex when the new ids are empty, so its `cache` would keep the old free ids (`Freed` true, `Free` panicking): the premise (the new free pages are not empty, or no page was free) excludes it (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). Through the interface (`flCall`): proved from `array.Read.spec`, `hashMap.Read.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Read.spec : Prop := ∀ fl, Interface.Read.contract (GF := GF) fl (flCall fl go!"Read")

end spec

end Freelist
end EtcdGrove
end Perennial
