/-
## `(*Page).FreelistPageIds()` (`internal/common/page.go`)

**Users.** freelist `Read` (and `Reload`, through it): the ids are copied out (`copy(idsCopy, ids)`), through `freelistIds_view`. Snippet `ReqWriteReload` (freelist's).
**Proof sketch.** `FreelistPageCount`, `UnsafeIndex`, `unsafe.Slice`: inside the page's bytes by `freelistReadable`.
**Changes.** from `specs-ref`'s file of the same name: over the page's bytes; the ids through `freelistIds_view` instead of a slice of a typed tail.
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

/-- `p.FreelistPageIds()`: the `[]Pgid` over the page's ids (`freelistIdsSlice`; `nil` if none), whose contents `freelistIds_view` lends. -/
def Page.FreelistPageIds.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜freelistReadable bs⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"FreelistPageIds")) (Val #()))
  {{ RET #(freelistIdsSlice p bs); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
