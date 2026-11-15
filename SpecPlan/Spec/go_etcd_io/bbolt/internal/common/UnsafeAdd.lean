/-
## `UnsafeAdd(base, offset)` (`internal/common/unsafe.go`)

**Users.** `Page.Meta`, `LeafPageElements`, `BranchPageElements`; freelist `Write`.
**Proof sketch.** `unsafe.Add`.
**Changes.** from `specs-ref`'s file of the same name: premises moved into the precondition.
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

/-- (internal) `UnsafeAdd(base, offset)`: `base` moved by `offset` bytes, for a result in `[0, maxAddr]`. -/
def UnsafeAdd.spec : Prop :=
  ∀ (base : Loc) (offset : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ ⌜0 ≤ (base +ₗ sint.Z offset).addr ∧ (base +ₗ sint.Z offset).addr ≤ maxAddr⌝ }}
    (App (App (Val (@! go_etcd_io.bbolt.internal.common.UnsafeAdd)) (Val #base)) (Val #offset))
  {{ RET #(base +ₗ sint.Z offset); True }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
