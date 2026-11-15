/-
## `(*InBucket).InlinePage(v)` (`internal/common/bucket.go`)

**Users.** none in bbolt (it takes `&value[BucketHeaderSize]` itself, bucket.go:140); kept as the API's statement of the inline page's address.
**Proof sketch.** the index check, `&v[16]` (Perennial's `sliceIndexRef_byte`, the slice's pointer positive by its points-to).
**Changes.** from `specs-ref`'s file of the same name: the address premises replaced by the value's bytes.
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

/-- `b.InlinePage(v)`: the inline page's address, after the bucket header (`&v[16]`); `b` is not read. It panics unless `v` is longer than the header: a premise. -/
def InBucket.InlinePage.spec : Prop :=
  ∀ (l : Loc) (v : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ v ↦*{dq} bs ∗ ⌜bucketHeaderSize < bs.length⌝ }}
    (App (Val (l @!! go.GoType.PointerType InBucket.ty @!! go!"InlinePage")) (Val #v))
  {{ RET #(v.ptr +ₗ (bucketHeaderSize : Int)); v ↦*{dq} bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
