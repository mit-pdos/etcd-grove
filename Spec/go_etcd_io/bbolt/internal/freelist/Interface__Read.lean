/-
## `Interface.Read(p)` (`shared.go`)

**Users.** db.go:460 (`loadFreelist`: the synced freelist page, into a new freelist); `Reload` (internal). Snippet `ReqWriteReload`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; `IsFreelistPage`, `FreelistPageIds` and `freelistIds_view` (`BboltCommon`), a copy, `sort.Sort` (the bound), `Init`.
**Changes.** from `specs-ref`'s `Interface__Read.lean`: from any state whose pending pages are not on the page (not only the empty one).
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

/-- `f.Read(p)`: the free pages are the freelist page's ids. It panics on a page of another kind or a count above `2^63` (`freelistReadable`); its ids must be distinct, from 2 on, and none pending (`Init`'s premise once sorted). -/
def Interface.Read.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ bytesPointsto p dq bs ∗
      ⌜freelistReadable bs ∧ (freelistIdsOf bs).Nodup ∧ (∀ x ∈ freelistIdsOf bs, 2 ≤ x.toNat) ∧
        (∀ x ∈ freelistIdsOf bs, x ∉ F.pending) ∧ (freelistIdsOf bs).length < flMaxIds⌝ }}
    (App (flCall fl go!"Read") (Val #p))
  {{ RET #(); flOwn fl (F.init (freelistIdsOf bs)) ∗ bytesPointsto p dq bs }}

end spec

end Freelist
end EtcdGrove
end Perennial
