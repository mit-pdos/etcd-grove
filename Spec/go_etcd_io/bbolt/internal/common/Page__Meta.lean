/-
## `(*Page).Meta()` (`internal/common/page.go`)

**Users.** db.go:396,436 (`getPageSize`), db.go:579-580 (`mmap`: `meta0`, `meta1`), db.go:695 (`init`), tx.go:448-453 (`writeMeta`); `Meta.Write`. Snippet `ReqMetaRoundTrip`.
**Proof sketch.** `UnsafeAdd(p, 16)`; the result is inside the page's bytes, so in `[0, maxAddr]` (a non-empty `bytesPointsto` lies in `(0, maxAddr]`). The meta itself is reached by `meta_view`.
**Changes.** from `specs-ref`'s file of the same name: the address premises replaced by the page's bytes (any share), which imply them.
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

/-- `p.Meta()`: the address of the meta after the header (`metaLoc p`). -/
def Page.Meta.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜pageHeaderSize + metaSize ≤ bs.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"Meta")) (Val #()))
  {{ RET #(metaLoc p); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
