/-
## `Interface.AddReadonlyTXID(tid)` (`shared.go`)

**Users.** db.go:896 (`beginTx`, under `metalock`, while a writer may use the freelist). Snippet `ReqReleaseSafe`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; an `append` to `readonlyTXIDs` (`flReaders`' field only).
**Changes.** new: the readers are their own resource (`flReaders`), separate from `flOwn`, so that `beginTx` needs no writer access (the old `flRoOwn`).
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

/-- The contract of `AddReadonlyTXID` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.AddReadonlyTXID(tid)`: `tid` is one more reader. -/
def Interface.AddReadonlyTXID.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (R : List Txid) (tid : Txid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flReaders fl R }}
    (App f (Val #tid))
  {{ RET #(); flReaders fl (R ++ [tid]) }}

/-- `f.AddReadonlyTXID(tid)`: `tid` is one more reader. Through the interface (`flCall`): proved from `array.AddReadonlyTXID.spec`, `hashMap.AddReadonlyTXID.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.AddReadonlyTXID.spec : Prop := ∀ fl, Interface.AddReadonlyTXID.contract (GF := GF) fl (flCall fl go!"AddReadonlyTXID")

end spec

end Freelist
end EtcdGrove
end Perennial
