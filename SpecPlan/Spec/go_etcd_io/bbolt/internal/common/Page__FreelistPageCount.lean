/-
## `(*Page).FreelistPageCount()` (`internal/common/page.go`)

**Users.** `FreelistPageIds` (none in bbolt).
**Proof sketch.** flags check, `count`, and for `0xFFFF` the first `Pgid` after the header through its view.
**Changes.** from `specs-ref`'s file of the same name: over the page's bytes (`freelistCount`, `freelistReadable`).
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

/-- `p.FreelistPageCount()`: the index of the first id and the number of ids (`freelistCount`). It panics on a page of another kind or a count above `2^63`: `freelistReadable` excludes both. -/
def Page.FreelistPageCount.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜freelistReadable bs⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"FreelistPageCount")) (Val #()))
  {{ RET (PairV #(W64 ((freelistCount bs).1 : Int)) #(W64 ((freelistCount bs).2 : Int)));
      bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
