/-
## `Interface.Reload(p)` (`shared.go`)

**Users.** tx.go:346 (`rollback` with a synced freelist: back to the committed freelist page, minus what is still pending). Snippet `ReqWriteReload`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; `Read(p)` (its `Init` may make pending pages free for a moment, inside this call), then `NoSyncReload(freePageIds())`.
**Changes.** from `specs-ref`'s `Interface__Reload.lean`: over `FLState`.
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

/-- `f.Reload(p)`: the free pages are the freelist page's ids but the pending ones. -/
def Interface.Reload.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ bytesPointsto p dq bs ∗
      ⌜freelistReadable bs ∧ (freelistIdsOf bs).Nodup ∧ (∀ x ∈ freelistIdsOf bs, 2 ≤ x.toNat) ∧
        (freelistIdsOf bs).length < flMaxIds ∧ F.count < flMaxIds⌝ }}
    (App (flCall fl go!"Reload") (Val #p))
  {{ RET #(); flOwn fl (F.reload (freelistIdsOf bs)) ∗ bytesPointsto p dq bs }}

end spec

end Freelist
end EtcdGrove
end Perennial
