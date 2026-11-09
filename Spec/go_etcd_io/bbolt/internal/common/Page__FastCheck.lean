/-
## `(*Page).FastCheck(id)` (`internal/common/page.go`)

**Users.** tx.go:639,646 (`Tx.page`: every page a transaction reads, from its dirty pages or the mmap). Snippet `ReqElementKeys`.
**Proof sketch.** `Id()`, `IsValidPage()`; both panics are excluded by the premise.
**Changes.** from `specs-ref`'s file of the same name: over the page's bytes; the premise as the decoded header.
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

/-- `p.FastCheck(id)`: returns when the page says it is page `id` and its flags are one page kind's; it panics otherwise, which the premise excludes (a caller knows it from the page's writer: `writeNode_read`, `freelistPage_read`, `Meta.Write`). -/
def Page.FastCheck.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8) (id : Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗
      ⌜pageHeaderSize ≤ bs.length ∧ (hdrOf bs).id' = id ∧ pageFlagValid (hdrOf bs).flags' = true⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"FastCheck")) (Val #id))
  {{ RET #(); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
