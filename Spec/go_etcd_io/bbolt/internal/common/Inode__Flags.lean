/-
## `(*Inode).Flags()` (`internal/common/inode.go`)

**Users.** cursor.go:381 (`keyValue`), bucket.go:822, node.go (`del`, `dereference`).
**Proof sketch.** one field load.
**Changes.** from `specs-ref`'s file of the same name (unchanged).
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Api

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

/-- `in.Flags()`: the field `flags`. -/
def Inode.Flags.spec : Prop :=
  ∀ (l : Loc) (v : Inode) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Inode.ty @!! go!"Flags")) (Val #()))
  {{ RET #(v.flags'); l ↦{dq} v }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
