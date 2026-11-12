/-
## `(*leafPageElement).IsBucketEntry()` (`internal/common/page.go`)

**Users.** tx_check.go:110 (`Check`).
**Proof sketch.** `flags & BucketLeafFlag`.
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

/-- `e.IsBucketEntry()` of element `i` of a page: whether its flags have `BucketLeafFlag`. -/
def leafPageElement.IsBucketEntry.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜elemOff (i + 1) ≤ bs.length⌝ }}
    (App (Val ((elemLoc p i) @!! go.GoType.PointerType leafPageElement.ty @!! go!"IsBucketEntry")) (Val #()))
  {{ RET #(decide ((leafElemOf bs i).flags' &&& bucketLeafFlag ≠ W32 0)); bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
