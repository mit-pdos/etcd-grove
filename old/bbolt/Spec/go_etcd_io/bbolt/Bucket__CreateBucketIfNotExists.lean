module
public import Proof.go_etcd_io.bbolt.WriteCreate

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

/-- `b.CreateBucketIfNotExists(key)` on a bucket of a write transaction: the nested bucket at
`key` (cached, or opened), or a new, empty inline bucket there (an error if the key holds a
value); the transaction stays a clean one, its buckets kept (the bucket opened added). -/
abbrev Bucket.CreateBucketIfNotExists.spec : Prop :=
  ∀ (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (key : GoSlice) (kb : List w8) (dk : DFrac),
  (T.bs !! bl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ key ↦*{dk} kb }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"CreateBucketIfNotExists")) (Val #key))
  {{ (rb : Loc) (err : GoInterface) (T' : WTx), RET (PairV #rb #err);
      ownWriteTx W txl T' ∗ ⌜wtxSub T T' ∧ (rb = null ∨ (T'.bs !! rb).isSome)⌝ ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
