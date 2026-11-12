/-
## `(*leafPageElement).Value()` (`internal/common/page.go`)

**Users.** cursor.go:386 (`keyValue`), bucket.go:659 (stats: `openBucket(e.Value())`). Snippet `ReqElementKeys`.
**Proof sketch.** `pos`, `ksize`, `vsize` through the element's view, then `UnsafeByteSlice(e, 0, i, j)`: inside the page's bytes by `leafElemIn`, so in the address space. The bytes are reached by `pageKV_access`.
**Changes.** from `specs-ref`'s file of the same name: relative to the page; the slice named (`leafValueSlice`) for `pageKV_access`.
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

/-- `e.Value()` of element `i` of a page: the slice of its value in the page (`leafValueSlice`; length and capacity its size). Nothing else is read. -/
def leafPageElement.Value.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜leafElemIn bs i⌝ }}
    (App (Val ((elemLoc p i) @!! go.GoType.PointerType leafPageElement.ty @!! go!"Value")) (Val #()))
  {{ RET #(leafValueSlice p bs i); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
