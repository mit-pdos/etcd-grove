module
public import Spec.go_etcd_io.bbolt.Bucket__CreateBucket

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

/-- `tx.CreateBucket(name)` in a write transaction: the root bucket's `CreateBucket(name)`
(`Bucket.CreateBucket.spec` on `&tx.root`). -/
abbrev Tx.CreateBucket.spec : Prop :=
  ∀ (W : WView) (txl : Loc) (T : WTx) (key : GoSlice) (kb : List w8) (dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ key ↦*{dk} kb }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"CreateBucket")) (Val #key))
  {{ (rb : Loc) (err : GoInterface) (T' : WTx), RET (PairV #rb #err);
      ownWriteTx W txl T' ∗ ⌜wtxSub T T' ∧ (rb = null ∨ (T'.bs !! rb).isSome)⌝ ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
