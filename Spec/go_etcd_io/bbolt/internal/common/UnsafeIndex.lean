/-
## `UnsafeIndex(base, offset, elemsz, n)` (`internal/common/unsafe.go`)

**Users.** `LeafPageElement`, `BranchPageElement`, `FreelistPageIds`.
**Proof sketch.** `unsafe.Add`.
**Changes.** from `specs-ref`'s file of the same name: premises moved into the precondition.
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

/-- (internal) `UnsafeIndex(base, offset, elemsz, n)`: element `n` of size `elemsz` of an array `offset` bytes past `base`. -/
def UnsafeIndex.spec : Prop :=
  ∀ (base : Loc) (offset elemsz n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ ⌜0 ≤ (base +ₗ sint.Z (offset + n * elemsz)).addr ∧
      (base +ₗ sint.Z (offset + n * elemsz)).addr ≤ maxAddr⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.bbolt.internal.common.UnsafeIndex)) (Val #base)) (Val #offset)) (Val #elemsz)) (Val #n))
  {{ RET #(base +ₗ sint.Z (offset + n * elemsz)); True }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
