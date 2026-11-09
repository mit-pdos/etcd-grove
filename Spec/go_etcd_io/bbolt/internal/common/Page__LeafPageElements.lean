/-
## `(*Page).LeafPageElements()` (`internal/common/page.go`)

**Users.** cursor.go:362 (`nsearch`: `inodes[i].Key()` under `sort.Search`), tx_check.go (`range`). Snippet `ReqElementKeys`.
**Proof sketch.** `Count()`, then `unsafe.Slice` of `count` elements at `p + 16`; the slice's elements are addressed by `elemsSlice_index`.
**Changes.** from `specs-ref`'s file of the same name: over the page's bytes; the result's elements named by `elemsSlice_index`.
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

/-- `p.LeafPageElements()`: the slice of the page's `count` elements (`nil` if none); `&s[i]` is `elemLoc p i` (`elemsSlice_index`). -/
def Page.LeafPageElements.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜elemOff (pageCount bs) ≤ bs.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"LeafPageElements")) (Val #()))
  {{ RET #(elemsSlice p (pageCount bs)); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
