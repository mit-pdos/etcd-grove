module
public import Spec.go_etcd_io.bbolt.Bucket__NextSequence
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

/-- `Bucket.NextSequence.spec` with the transaction's shape: the bucket's root node, if it has none, is
materialized (`Bucket.node.sspec`); its header's sequence is not part of the shape. -/
abbrev Bucket.NextSequence.sspec : Prop :=
  ∀ (γ : GName) (W : WView) (txl : Loc) (T : WTx) (bl : Loc),
  (T.bs !! bl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ txShape γ W T }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"NextSequence")) (Val #()))
  {{ (n : w64) (err : GoInterface) (T' : WTx), RET (PairV #n #err);
      ownWriteTx W txl T' ∗ txShape γ W T' ∗ ⌜wtxSame T T'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
