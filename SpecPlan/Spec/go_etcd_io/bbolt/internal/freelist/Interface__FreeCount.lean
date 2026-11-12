/-
## `Interface.FreeCount()` (`shared.go`, `array.go`, `hashmap.go`)

**Users.** tx.go:359 (stats), db.go:467 (`loadFreelist`'s stats).
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; the counts are sums of lengths (an `int`: the bound).
**Changes.** from `specs-ref`'s `Interface__FreeCount.lean`: over `FLState`; the bound `flMaxIds` (a named constant) in place of `WF`'s `2^63`.
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

/-- The contract of `FreeCount` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.FreeCount()`: the number of free pages. -/
def Interface.FreeCount.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ ⌜F.count < flMaxIds⌝ }}
    (App f (Val #()))
  {{ RET #(W64 (F.free.domList.length : Int)); flOwn fl F }}

/-- `f.FreeCount()`: the number of free pages. Through the interface (`flCall`): proved from `array.FreeCount.spec`, `hashMap.FreeCount.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.FreeCount.spec : Prop := ∀ fl, Interface.FreeCount.contract (GF := GF) fl (flCall fl go!"FreeCount")

end spec

end Freelist
end EtcdGrove
end Perennial
