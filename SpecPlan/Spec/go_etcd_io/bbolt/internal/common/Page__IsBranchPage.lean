/-
## `(*Page).IsBranchPage()` (`internal/common/page.go`)

**Users.** bucket.go:663,731 (stats, `forEachPageNode`), cursor.go:285 (`goToFirstElementOnTheStack`).
**Proof sketch.** one load of `flags` through the header's view.
**Changes.** from `specs-ref`'s file of the same name: over the page's bytes.
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

/-- `p.IsBranchPage()`: whether the header's flags are exactly `branchPageFlag`. -/
def Page.IsBranchPage.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜pageHeaderSize ≤ bs.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"IsBranchPage")) (Val #()))
  {{ RET #(decide ((hdrOf bs).flags' = branchPageFlag)); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
