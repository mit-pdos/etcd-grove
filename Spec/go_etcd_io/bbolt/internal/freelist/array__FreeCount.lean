/-
## `(*array).FreeCount` (`array.go`)

**Users.** through the interface: `Interface.FreeCount.spec`'s bundle is proved from this spec and its `hashMap` twin.
**Proof sketch.** the realization of `flOwn` at a `*array` (its fields and `shared`'s, with the model's invariant) and the method's body, as in `Interface.FreeCount`'s sketch.
**Changes.** new: the canonical (type, method) spec (PRINCIPLES, "Canonical specs are per (concrete type, method)"), an instance of the interface's contract.
**Margin.** as `Interface.FreeCount.spec`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__FreeCount

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

/-- `FreeCount` on a `*array`: `Interface.FreeCount`'s contract at `arrayIface l`. -/
def array.FreeCount.spec : Prop := ∀ (l : Loc),
  Interface.FreeCount.contract (GF := GF) (arrayIface l) (Val (l @!! go.GoType.PointerType go_etcd_io.bbolt.internal.freelist.array'.ty @!! go!"FreeCount"))

end spec

end Freelist
end EtcdGrove
end Perennial
