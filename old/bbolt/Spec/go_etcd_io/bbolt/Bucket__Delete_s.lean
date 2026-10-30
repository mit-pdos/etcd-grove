module
public import Proof.go_etcd_io.bbolt.WriteTxAcc
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

/-- `b.Delete(key)` on a bucket of a write transaction: the transaction stays a clean one, with
the same buckets (the key removed from the leaf a cursor finds it in, if there), and its shape
(`txShape`). -/
abbrev Bucket.Delete.sspec : Prop :=
  ∀ (γ : GName) (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (key : GoSlice) (kb : List w8) (dk : DFrac),
  (T.bs !! bl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ key ↦*{dk} kb ∗
      txShape γ W T }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Delete")) (Val #key))
  {{ (err : GoInterface) (T' : WTx), RET #err;
      ownWriteTx W txl T' ∗ ⌜wtxSame T T'⌝ ∗ txShape γ W T' ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
