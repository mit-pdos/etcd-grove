/-
## `(*InBucket).IncSequence()` (`internal/common/bucket.go`)

**Users.** bucket.go:577 (`NextSequence`).
**Proof sketch.** a load and a store (wrapping).
**Changes.** from `specs-ref`'s file of the same name (unchanged).
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

/-- `b.IncSequence()`: the sequence plus one (wrapping). -/
def InBucket.IncSequence.spec : Prop :=
  ∀ (l : Loc) (v : InBucket),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType InBucket.ty @!! go!"IncSequence")) (Val #()))
  {{ RET #(); l ↦ ({ v with sequence' := v.sequence' + W64 1 } : InBucket) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
