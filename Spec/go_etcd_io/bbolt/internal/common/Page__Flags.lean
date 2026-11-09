/-
## `(*Page).Flags()` (`internal/common/page.go`)

**Users.** node.go:180 (`node.write`'s assert), cursor.go:286 (panic message). Snippets `ReqNodeRoundTrip`, `ReqElementKeys`.
**Proof sketch.** the view of the header's 16 bytes as a typed `Page` (Perennial's `bytesPointsto_view_read`, the package's `BytesView Page`), one field load.
**Changes.** from `specs-ref`'s file of the same name: over the page's bytes (`hdrOf`) instead of a typed header points-to, so a client holding the bytes of a page (mmap, buffer, value) calls it without a view.
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

/-- `p.Flags()`: the header's `flags` field, decoded from the page's bytes (any share). -/
def Page.Flags.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜pageHeaderSize ≤ bs.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"Flags")) (Val #()))
  {{ RET #((hdrOf bs).flags'); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
