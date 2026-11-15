/-
## `(*branchPageElement).Key()` (`internal/common/page.go`)

**Users.** cursor.go:332 (`searchPage`), tx_check.go:202,206; `ReadInodeFromPage`. Snippet `ReqElementKeys`.
**Proof sketch.** `pos`, `ksize`, `UnsafeByteSlice`; inside the page by `branchElemIn`.
**Changes.** from `specs-ref`'s file of the same name: relative to the page.
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

/-- `e.Key()` of element `i` of a branch page: the slice of its key in the page (`branchKeySlice`). -/
def branchPageElement.Key.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜branchElemIn bs i⌝ }}
    (App (Val ((elemLoc p i) @!! go.GoType.PointerType branchPageElement.ty @!! go!"Key")) (Val #()))
  {{ RET #(branchKeySlice p bs i); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
