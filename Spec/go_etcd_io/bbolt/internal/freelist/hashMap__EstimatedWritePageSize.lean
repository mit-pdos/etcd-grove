/-
## `(*hashMap).EstimatedWritePageSize` (`shared.go`, promoted through the embedded `*shared`)

**Users.** through the interface: `Interface.EstimatedWritePageSize.spec`'s bundle is proved from this spec and its `array` twin.
**Proof sketch.** the realization of `flOwn` at a `*hashMap` (its fields and `shared`'s, with the model's invariant) and the method's body (`shared`'s, reached through the promotion: the field `shared`, read-only after the constructor), as in `Interface.EstimatedWritePageSize`'s sketch.
**Changes.** new: the canonical (type, method) spec (PRINCIPLES, "Canonical specs are per (concrete type, method)"), an instance of the interface's contract.
**Margin.** as `Interface.EstimatedWritePageSize.spec`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__EstimatedWritePageSize

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

/-- `EstimatedWritePageSize` on a `*hashMap`: `Interface.EstimatedWritePageSize`'s contract at `hashMapIface l`. -/
def hashMap.EstimatedWritePageSize.spec : Prop := ∀ (l : Loc),
  Interface.EstimatedWritePageSize.contract (GF := GF) (hashMapIface l) (Val (l @!! go.GoType.PointerType go_etcd_io.bbolt.internal.freelist.hashMap.ty @!! go!"EstimatedWritePageSize"))

end spec

end Freelist
end EtcdGrove
end Perennial
