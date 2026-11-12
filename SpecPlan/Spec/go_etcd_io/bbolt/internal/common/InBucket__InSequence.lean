/-
## `(*InBucket).InSequence()` (`internal/common/bucket.go`)

**Users.** bucket.go:540 (`Sequence`). Snippet `ReqInlineBucket`.
**Proof sketch.** one field load.
**Changes.** from `specs-ref`'s file of the same name (unchanged; a header in a value is reached by `inBucket_view`).
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

/-- `b.InSequence()`: the field `sequence`. -/
def InBucket.InSequence.spec : Prop :=
  ∀ (l : Loc) (v : InBucket) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType InBucket.ty @!! go!"InSequence")) (Val #()))
  {{ RET #(v.sequence'); l ↦{dq} v }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
