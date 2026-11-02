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

/-- `b.Put(key, value)` on a bucket of a write transaction: the transaction stays a clean one,
with the same buckets (the key put in the leaf a cursor finds for it). On success the value's
bytes stay with the transaction (bbolt keeps the slice: it must stay valid, and unchanged, for
the transaction's life); on an error they come back. The transaction keeps its shape
(`txShape`). -/
abbrev Bucket.Put.sspec : Prop :=
  ∀ (γ : GName) (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (key value : GoSlice) (kb vb : List w8)
    (dk dv : DFrac),
  (T.bs !! bl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ key ↦*{dk} kb ∗
      value ↦*{dv} vb ∗ txShape γ W T }}
    (App (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Put")) (Val #key)) (Val #value))
  {{ (err : GoInterface) (T' : WTx), RET #err;
      ownWriteTx W txl T' ∗ ⌜wtxSame T T'⌝ ∗ txShape γ W T' ∗ key ↦*{dk} kb ∗
      (⌜err = interface.nil⌝ ∨ ⌜err ≠ interface.nil⌝ ∗ value ↦*{dv} vb) }}

end spec

end bbolt
end EtcdGrove
end Perennial
