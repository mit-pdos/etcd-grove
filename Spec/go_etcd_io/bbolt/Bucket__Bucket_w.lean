module
public import Proof.go_etcd_io.bbolt.WriteBucket

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

/-- `b.Bucket(name)` on a bucket of a write transaction: the nested bucket `name` (cached, or
opened from its value and cached), or nil; the transaction stays a clean one, its buckets kept
(the opened one added). -/
abbrev Bucket.Bucket.wspec : Prop :=
  ∀ (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (name : GoSlice) (nb : List w8) (dk : DFrac),
  (T.bs !! bl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ name ↦*{dk} nb }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Bucket")) (Val #name))
  {{ (cl : Loc) (T' : WTx), RET #cl;
      ownWriteTx W txl T' ∗ ⌜wtxSub T T' ∧ (cl = null ∨ (T'.bs !! cl).isSome)⌝ ∗ name ↦*{dk} nb }}

end spec

end bbolt
end EtcdGrove
end Perennial
