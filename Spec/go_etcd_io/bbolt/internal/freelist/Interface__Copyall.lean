/-
## `Interface.Copyall(dst)` (`shared.go`)

**Users.** tx_check.go:50 (`Check`); `Write` (internal).
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; the pending ids gathered and sorted (`sort.Sort`: the bound), `freePageIds()` (sorted), `Mergepgids` (`BboltCommon`).
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

/-- The contract of `Copyall` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Copyall(dst)`: the first `Count()` elements of `dst` become the free and pending ids, sorted (`FLState.ids`); the rest is untouched. It panics if `dst` is too short: a premise. -/
def Interface.Copyall.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (dst : GoSlice) (ds : List Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ dst ↦* ds ∗ ⌜F.count ≤ ds.length ∧ F.count < flMaxIds⌝ }}
    (App f (Val #dst))
  {{ RET #(); flOwn fl F ∗ dst ↦* (F.ids ++ ds.drop F.count) }}

/-- `f.Copyall(dst)`: the first `Count()` elements of `dst` become the free and pending ids, sorted (`FLState.ids`); the rest is untouched. It panics if `dst` is too short: a premise. Through the interface (`flCall`): proved from `array.Copyall.spec`, `hashMap.Copyall.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Copyall.spec : Prop := ∀ fl, Interface.Copyall.contract (GF := GF) fl (flCall fl go!"Copyall")

end spec

end Freelist
end EtcdGrove
end Perennial
