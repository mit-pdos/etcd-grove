/-
## `UnsafeByteSlice(base, offset, i, j)` (`internal/common/unsafe.go`)

**Users.** tx.go:549 (`Tx.write`: a page's bytes in `MaxAllocSize - 1` chunks for `WriteAt`), tx.go:588 (`Tx.write`: a page-pool buffer to zero); element `Key`/`Value`, `WriteInodeToPage`. Snippet `ReqPageSortWrite`.
**Proof sketch.** `unsafe.Add`, `unsafe.Slice`, a full slice expression.
**Changes.** from `specs-ref`'s file of the same name: premises moved into the precondition. A client turns the result into the bytes it covers with Perennial's `ownSlice_byte_view`.
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

/-- `UnsafeByteSlice(base, offset, i, j)`: the bytes `[offset + i, offset + j)` from `base` as a slice of length and capacity `j - i`. It panics unless `0 ≤ i ≤ j`, and the memory must lie in the address space: premises. -/
def UnsafeByteSlice.spec : Prop :=
  ∀ (base : Loc) (offset i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ ⌜0 < (base +ₗ sint.Z offset).addr ∧ (base +ₗ sint.Z offset).addr + sint.Z j ≤ maxAddr ∧
      0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.bbolt.internal.common.UnsafeByteSlice)) (Val #base)) (Val #offset)) (Val #i)) (Val #j))
  {{ RET #(slice.mk ((base +ₗ sint.Z offset) +ₗ sint.Z i) (j - i) (j - i)); True }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
