/-
## `(*Inode).SetKey(x)` (`internal/common/inode.go`)

**Users.** node.go:137-140 (`put`), node.go:482,487 (`dereference`); `ReadInodeFromPage`.
**Proof sketch.** one field store.
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

/-- `in.SetKey(x)` writes the field `key`. -/
def Inode.SetKey.spec : Prop :=
  ∀ (l : Loc) (v : Inode) (x : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType Inode.ty @!! go!"SetKey")) (Val #x))
  {{ RET #(); l ↦ ({ v with key' := x } : Inode) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
