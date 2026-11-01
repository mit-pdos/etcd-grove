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

/-- `ForEach`'s closure `fn`: called on a key and value of the bucket (`kvElem`; the value nil
for a nested bucket), lent to it, with the caller's resources `I` (say, a part of the bucket,
to read it while the iteration's cursor is open) and the transaction's statistics (to create
cursors); it returns them, and an error. -/
def forEachFn (fn : GoFunc) (V : BktView) (I : IProp GF) : IProp GF :=
  iprop(∀ (k v : GoSlice) (kb vb : List w8) (dq : DFrac),
    {{ I ∗ txStats V.tx ∗ k ↦*{dq} kb ∗ v ↦*{dq} vb ∗ ⌜kvElem V kb vb v⌝ }}
      (App (App (Val #fn) (Val #k)) (Val #v))
    {{ (err : GoInterface), RET #err; I ∗ txStats V.tx ∗ k ↦*{dq} kb ∗ v ↦*{dq} vb }})

instance forEachFn_persistent (fn : GoFunc) (V : BktView) (I : IProp GF) :
    Iris.BI.Persistent (forEachFn fn V I) := by
  unfold forEachFn; infer_instance

/-- `b.ForEach(fn)` on the read path: `fn` on every key and value of the bucket, in order,
until it returns an error (which `ForEach` returns; nil otherwise). -/
abbrev Bucket.ForEach.spec : Prop :=
  ∀ (bl : Loc) (V : BktView) (q : Qp) (fn : GoFunc) (I : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktR bl V q ∗ txStats V.tx ∗ I ∗
      □ forEachFn fn V I }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; bktR bl V q ∗ txStats V.tx ∗ I }}

end spec

end bbolt
end EtcdGrove
end Perennial
