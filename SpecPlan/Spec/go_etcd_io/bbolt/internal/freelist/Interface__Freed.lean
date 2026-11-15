/-
## `Interface.Freed(id)` (`shared.go`)

**Users.** tx.go:694 (`Tx.Page`: a page's info for tools; it reads the freelist without `rwlock`, so a client needs the writer's resource there).
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; a lookup in `cache`, which holds the free and pending ids.
**Changes.** new (no old spec).
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

/-- The contract of `Freed` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Freed(id)`: whether page `id` is free or pending. -/
def Interface.Freed.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (id : Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F }}
    (App f (Val #id))
  {{ RET #(decide (id ∈ F.free ∨ id ∈ F.pending)); flOwn fl F }}

/-- `f.Freed(id)`: whether page `id` is free or pending. Through the interface (`flCall`): proved from `array.Freed.spec`, `hashMap.Freed.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Freed.spec : Prop := ∀ fl, Interface.Freed.contract (GF := GF) fl (flCall fl go!"Freed")

end spec

end Freelist
end EtcdGrove
end Perennial
