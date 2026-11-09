/-
## `(*Page).PageElementSize()` (`internal/common/page.go`)

**Users.** `WriteInodeToPage` (internal).
**Proof sketch.** `IsLeafPage()`; both constants are 16.
**Changes.** from `specs-ref`'s file of the same name: over the page's bytes.
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

/-- (internal) `p.PageElementSize()`: 16, a leaf's or a branch's element size. -/
def Page.PageElementSize.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜pageHeaderSize ≤ bs.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"PageElementSize")) (Val #()))
  {{ RET #(W64 (elemSize : Int)); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
