module
public import Spec.go_etcd_io.bbolt.Bucket__Bucket

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

/-- `Tx.ForEach`'s closure `fn`: called on a key of the root bucket (lent to it) and the nested
bucket it names (nil if it is no bucket), with the caller's resources `I` and the transaction's
statistics; it returns them, the nested bucket, and an error. -/
def txForEachFn (fn : GoFunc) (V : BktView) (I : IProp GF) : IProp GF :=
  iprop(∀ (k : GoSlice) (kb : List w8) (dq : DFrac) (cl : Loc) (V' : BktView) (qc : Qp),
    {{ I ∗ txStats V.tx ∗ k ↦*{dq} kb ∗ (⌜cl = null⌝ ∨ ⌜nestedOK V V' kb⌝ ∗ bktR cl V' qc) }}
      (App (App (Val #fn) (Val #k)) (Val #cl))
    {{ (err : GoInterface), RET #err; I ∗ txStats V.tx ∗ k ↦*{dq} kb ∗
        (⌜cl = null⌝ ∨ bktR cl V' qc) }})

instance txForEachFn_persistent (fn : GoFunc) (V : BktView) (I : IProp GF) :
    Iris.BI.Persistent (txForEachFn fn V I) := by
  unfold txForEachFn; infer_instance

/-- `tx.ForEach(fn)` in a read transaction: `fn` on every key of the root bucket and the nested
bucket it names, in order, until it returns an error (which `ForEach` returns; nil
otherwise). -/
abbrev Tx.ForEach.spec : Prop :=
  ∀ (txl : Loc) (V : BktView) (q : Qp) (fn : GoFunc) (I : IProp GF),
  V.bkt.buckets' = map.nil → V.txv.writable' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      bktR (structFieldRef Tx go!"root" txl) V q ∗ txStats V.tx ∗ I ∗ □ txForEachFn fn V I }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; bktR (structFieldRef Tx go!"root" txl) V q ∗ txStats V.tx ∗ I }}

end spec

end bbolt
end EtcdGrove
end Perennial
