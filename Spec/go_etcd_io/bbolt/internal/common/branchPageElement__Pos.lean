/-
## `(*branchPageElement).Pos()` (`internal/common/page.go`)

**Users.** bucket.go:676 (stats); `ReadInodeFromPage`. Snippet `ReqElementKeys`.
**Proof sketch.** the element's typed view, one field load.
**Changes.** from `specs-ref`'s file of the same name: relative to the page holding the element.
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

/-- `e.Pos()` of element `i` of a page: its `pos` field (`branchElemOf`). -/
def branchPageElement.Pos.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜elemOff (i + 1) ≤ bs.length⌝ }}
    (App (Val ((elemLoc p i) @!! go.GoType.PointerType branchPageElement.ty @!! go!"Pos")) (Val #()))
  {{ RET #((branchElemOf bs i).pos'); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
