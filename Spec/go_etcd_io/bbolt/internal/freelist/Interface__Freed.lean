/-
## `Interface.Freed(id)` (`shared.go`)

**Users.** tx.go:694 (`Tx.Page`: a page's info for tools; it reads the freelist without `rwlock`, so a client needs the writer's resource there).
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; a lookup in `cache`, which holds the free and pending ids.
**Changes.** new (no old spec).
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

/-- `f.Freed(id)`: whether page `id` is free or pending. -/
def Interface.Freed.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (id : Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F }}
    (App (flCall fl go!"Freed") (Val #id))
  {{ RET #(decide (id ∈ F.free ∨ id ∈ F.pending)); flOwn fl F }}

end spec

end Freelist
end EtcdGrove
end Perennial
