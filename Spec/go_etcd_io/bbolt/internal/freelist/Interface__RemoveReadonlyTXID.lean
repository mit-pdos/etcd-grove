/-
## `Interface.RemoveReadonlyTXID(tid)` (`shared.go`)

**Users.** db.go:957 (`removeTx`, under `metalock`). Snippet `ReqReleaseSafe`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; the first occurrence swapped with the last and dropped (a multiset removal, `flReaders_perm`).
**Changes.** new (as `AddReadonlyTXID`).
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

/-- The contract of `RemoveReadonlyTXID` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.RemoveReadonlyTXID(tid)`: one occurrence of `tid` is no longer a reader (none if it is not one). -/
def Interface.RemoveReadonlyTXID.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (R : List Txid) (tid : Txid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flReaders fl R }}
    (App f (Val #tid))
  {{ RET #(); flReaders fl (R.erase tid) }}

/-- `f.RemoveReadonlyTXID(tid)`: one occurrence of `tid` is no longer a reader (none if it is not one). Through the interface (`flCall`): proved from `array.RemoveReadonlyTXID.spec`, `hashMap.RemoveReadonlyTXID.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.RemoveReadonlyTXID.spec : Prop := ∀ fl, Interface.RemoveReadonlyTXID.contract (GF := GF) fl (flCall fl go!"RemoveReadonlyTXID")

end spec

end Freelist
end EtcdGrove
end Perennial
