/-
## `(*Inode).Value()` (`internal/common/inode.go`)

**Users.** cursor.go:381, node.go:45,57,284,485-486, bucket.go:820.
**Proof sketch.** one field load.
**Changes.** from `specs-ref`'s file of the same name (unchanged).
**Margin.** none: the post is what the code computes.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `in.Value()`: the field `value`. -/
def Inode.Value.spec : Prop :=
  ∀ (l : Loc) (v : Inode) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Inode.ty @!! go!"Value")) (Val #()))
  {{ RET #(v.value'); l ↦{dq} v }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
