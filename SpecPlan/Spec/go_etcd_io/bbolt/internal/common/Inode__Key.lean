/-
## `(*Inode).Key()` (`internal/common/inode.go`)

**Users.** cursor.go:309,355,381, node.go:45,57,83,127,130,147,150,169,284,347-351,480-483,543, bucket.go:820.
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

/-- `in.Key()`: the field `key`. -/
def Inode.Key.spec : Prop :=
  ∀ (l : Loc) (v : Inode) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Inode.ty @!! go!"Key")) (Val #()))
  {{ RET #(v.key'); l ↦{dq} v }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
