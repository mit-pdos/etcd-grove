/-
## `(*leafPageElement).Vsize()` (`internal/common/page.go`)

**Users.** bucket.go:639 (stats); `ReadInodeFromPage`. Snippet `ReqElementKeys`.
**Proof sketch.** the element's 16 bytes viewed as a typed `leafPageElement` (`bytesPointsto_view_read`), one field load.
**Changes.** from `specs-ref`'s file of the same name: relative to the page holding the element (`e = elemLoc p i`), so a client never takes an element's view.
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

/-- `e.Vsize()` of element `i` of a page: its `vsize` field (`leafElemOf`). -/
def leafPageElement.Vsize.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜elemOff (i + 1) ≤ bs.length⌝ }}
    (App (Val ((elemLoc p i) @!! go.GoType.PointerType leafPageElement.ty @!! go!"Vsize")) (Val #()))
  {{ RET #((leafElemOf bs i).vsize'); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
