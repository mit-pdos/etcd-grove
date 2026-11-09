/-
## `(*Page).LeafPageElement(i)` (`internal/common/page.go`)

**Users.** cursor.go:385 (`keyValue`), bucket.go:638,655 (stats), tx_check.go:109,215; `WriteInodeToPage`, `ReadInodeFromPage`. Snippet `ReqElementKeys`.
**Proof sketch.** `UnsafeIndex(p, 16, 16, i)`: `p + 16 + 16 i`, inside the page's bytes by the premise.
**Changes.** from `specs-ref`'s file of the same name: the address premises replaced by the page's bytes reaching the element.
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

/-- `p.LeafPageElement(i)`: the address of element `i` (`elemLoc p i`); nothing is read. -/
def Page.LeafPageElement.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8) (i : w16),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜elemOff (uint.nat i + 1) ≤ bs.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"LeafPageElement")) (Val #i))
  {{ RET #(elemLoc p (uint.nat i)); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
