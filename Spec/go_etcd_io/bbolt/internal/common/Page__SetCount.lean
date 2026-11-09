/-
## `(*Page).SetCount(v)` (`internal/common/page.go`)

**Users.** db.go:710,716 (`init`), node.go:192 (`node.write`), freelist `Write`. Snippet `ReqNodeRoundTrip`.
**Proof sketch.** the typed view of the header's bytes (`bytesPointsto_view`), one field store; the bytes after the header are untouched (`hdr_withHdr`).
**Changes.** from `specs-ref`'s file of the same name: over the page's bytes (`withHdr`).
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

/-- `p.SetCount(v)`: the header's `count` field becomes `v`, in the page's bytes (`withHdr`). -/
def Page.SetCount.spec : Prop :=
  ∀ (p : Loc) (bs : List w8) (v : w16),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p (DFrac.own 1) bs ∗ ⌜pageHeaderSize ≤ bs.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"SetCount")) (Val #v))
  {{ RET #(); bytesPointsto p (DFrac.own 1) (withHdr bs { hdrOf bs with count' := v }) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
