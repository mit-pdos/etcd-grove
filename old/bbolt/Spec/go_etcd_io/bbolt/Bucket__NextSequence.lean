module
public import Proof.go_etcd_io.bbolt.WriteTxAcc

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

/-- `b.NextSequence()` on a bucket of a write transaction (its root node materialized, its sequence incremented): the transaction stays a clean one, with the same buckets. -/
abbrev Bucket.NextSequence.spec : Prop :=
  ∀ (W : WView) (txl : Loc) (T : WTx) (bl : Loc),
  (T.bs !! bl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"NextSequence")) (Val #()))
  {{ (n : w64) (err : GoInterface) (T' : WTx), RET (PairV #n #err);
      ownWriteTx W txl T' ∗ ⌜wtxSame T T'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
