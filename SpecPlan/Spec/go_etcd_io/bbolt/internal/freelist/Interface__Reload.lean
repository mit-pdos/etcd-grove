/-
## `Interface.Reload(p)` (`shared.go`)

**Users.** tx.go:346 (`rollback` with a synced freelist: back to the committed freelist page, minus what is still pending). Snippet `ReqWriteReload`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; `Read(p)` (its `Init` may make pending pages free for a moment, inside this call), then `NoSyncReload(freePageIds())`.
**Changes.** from `specs-ref`'s `Interface__Reload.lean`: over `FLState`; round 1: the hash map's premise kept (F1), the count bound dropped (`Reload` sorts only the page's ids, S7).
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

/-- The contract of `Reload` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Reload(p)`: the free pages are the freelist page's ids but the pending ones. The hash map's `Init` returns before its reindex when the new ids are empty, so its `cache` would keep the old free ids: the premise (the page's ids are not empty, or no page was free) excludes it (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). (A non-empty page whose ids are all pending is fine: `Read`'s `Init` reindexes first.) -/
def Interface.Reload.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ bytesPointsto p dq bs ∗
      ⌜freelistReadable bs ∧ (freelistIdsOf bs).Nodup ∧ (∀ x ∈ freelistIdsOf bs, 2 ≤ x.toNat) ∧
        (freelistIdsOf bs).length < flMaxIds ∧ (freelistIdsOf bs ≠ [] ∨ F.free = GMap.empty)⌝ }}
    (App f (Val #p))
  {{ RET #(); flOwn fl (F.reload (freelistIdsOf bs)) ∗ bytesPointsto p dq bs }}

/-- `f.Reload(p)`: the free pages are the freelist page's ids but the pending ones. The hash map's `Init` returns before its reindex when the new ids are empty, so its `cache` would keep the old free ids: the premise (the page's ids are not empty, or no page was free) excludes it (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). (A non-empty page whose ids are all pending is fine: `Read`'s `Init` reindexes first.) Through the interface (`flCall`): proved from `array.Reload.spec`, `hashMap.Reload.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Reload.spec : Prop := ∀ fl, Interface.Reload.contract (GF := GF) fl (flCall fl go!"Reload")

end spec

end Freelist
end EtcdGrove
end Perennial
