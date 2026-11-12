/-
## `(*array).AddReadonlyTXID` (`shared.go`, promoted through the embedded `*shared`)

**Users.** through the interface: `Interface.AddReadonlyTXID.spec`'s bundle is proved from this spec and its `hashMap` twin.
**Proof sketch.** the realization of `flOwn` at a `*array` (its fields and `shared`'s, with the model's invariant) and the method's body (`shared`'s, reached through the promotion: the field `shared`, read-only after the constructor), as in `Interface.AddReadonlyTXID`'s sketch.
**Changes.** new: the canonical (type, method) spec (PRINCIPLES, "Canonical specs are per (concrete type, method)"), an instance of the interface's contract.
**Margin.** as `Interface.AddReadonlyTXID.spec`.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.freelist.Interface__AddReadonlyTXID

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

/-- `AddReadonlyTXID` on a `*array`: `Interface.AddReadonlyTXID`'s contract at `arrayIface l`. -/
def array.AddReadonlyTXID.spec : Prop := ∀ (l : Loc),
  Interface.AddReadonlyTXID.contract (GF := GF) (arrayIface l) (Val (l @!! go.GoType.PointerType go_etcd_io.bbolt.internal.freelist.array'.ty @!! go!"AddReadonlyTXID"))

end spec

end Freelist
end EtcdGrove
end Perennial
