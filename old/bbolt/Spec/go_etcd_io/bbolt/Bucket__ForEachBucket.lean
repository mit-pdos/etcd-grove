module
public import Proof.go_etcd_io.bbolt.BucketIter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `ForEachBucket`'s closure `fn`: called on the name of a nested bucket of the bucket
(`bktElem`), lent to it, with the caller's resources `I` and the transaction's statistics; it
returns them, and an error. -/
def forEachBucketFn (fn : GoFunc) (V : BktView) (I : IProp GF) : IProp GF :=
  iprop(∀ (k : GoSlice) (kb : List w8) (dq : DFrac),
    {{ I ∗ txStats V.tx ∗ k ↦*{dq} kb ∗ ⌜bktElem V kb⌝ }}
      (App (Val #fn) (Val #k))
    {{ (err : GoInterface), RET #err; I ∗ txStats V.tx ∗ k ↦*{dq} kb }})

instance forEachBucketFn_persistent (fn : GoFunc) (V : BktView) (I : IProp GF) :
    Iris.BI.Persistent (forEachBucketFn fn V I) := by
  unfold forEachBucketFn; infer_instance

/-- `b.ForEachBucket(fn)` on the read path: `fn` on the name of every nested bucket of the
bucket, in order, until it returns an error (which `ForEachBucket` returns; nil otherwise). -/
abbrev Bucket.ForEachBucket.spec : Prop :=
  ∀ (bl : Loc) (V : BktView) (q : Qp) (fn : GoFunc) (I : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktR bl V q ∗ txStats V.tx ∗ I ∗
      □ forEachBucketFn fn V I }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"ForEachBucket")) (Val #fn))
  {{ (err : GoInterface), RET #err; bktR bl V q ∗ txStats V.tx ∗ I }}

end spec

end bbolt
end EtcdGrove
end Perennial
