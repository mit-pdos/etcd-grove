/-
## `(*InBucket).SetInSequence(x)` (`internal/common/bucket.go`)

**Users.** bucket.go:558 (`SetSequence`).
**Proof sketch.** one field store.
**Changes.** from `specs-ref`'s file of the same name (unchanged).
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

/-- `b.SetInSequence(x)` writes the field `sequence`. -/
def InBucket.SetInSequence.spec : Prop :=
  ∀ (l : Loc) (v : InBucket) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType InBucket.ty @!! go!"SetInSequence")) (Val #x))
  {{ RET #(); l ↦ ({ v with sequence' := x } : InBucket) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
