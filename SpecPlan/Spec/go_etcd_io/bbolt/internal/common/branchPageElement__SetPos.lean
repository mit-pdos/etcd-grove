/-
## `(*branchPageElement).SetPos(v)` (`internal/common/page.go`)

**Users.** `WriteInodeToPage` only (internal).
**Proof sketch.** one field store.
**Changes.** from `specs-ref`'s file of the same name (unchanged: an internal setter over the typed element, which `WriteInodeToPage`'s proof views).
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

/-- (internal) `e.SetPos(v)` writes the field `pos`. -/
def branchPageElement.SetPos.spec : Prop :=
  ∀ (e : Loc) (v : branchPageElement) (x : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ e ↦ v }}
    (App (Val (e @!! go.GoType.PointerType branchPageElement.ty @!! go!"SetPos")) (Val #x))
  {{ RET #(); e ↦ ({ v with pos' := x } : branchPageElement) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
