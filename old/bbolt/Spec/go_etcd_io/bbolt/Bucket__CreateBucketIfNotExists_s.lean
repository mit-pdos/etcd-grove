module
public import Spec.go_etcd_io.bbolt.Bucket__CreateBucketIfNotExists
public import Proof.go_etcd_io.bbolt.WriteTxShape

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.CreateBucketIfNotExists(key)` (`Bucket.CreateBucketIfNotExists.spec`) with the transaction's
shape: a bucket it opens takes its entry's tree's tokens (`Bucket.Bucket.sspec`); a new inline
bucket's entry, put into the leaf the cursor found, holds no page. -/
abbrev Bucket.CreateBucketIfNotExists.sspec : Prop :=
  ∀ (γ : GName) (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (key : GoSlice) (kb : List w8) (dk : DFrac),
  (T.bs !! bl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ txShape γ W T ∗
      key ↦*{dk} kb }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"CreateBucketIfNotExists")) (Val #key))
  {{ (rb : Loc) (err : GoInterface) (T' : WTx), RET (PairV #rb #err);
      ownWriteTx W txl T' ∗ txShape γ W T' ∗ ⌜wtxSub T T' ∧ (rb = null ∨ (T'.bs !! rb).isSome)⌝ ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
