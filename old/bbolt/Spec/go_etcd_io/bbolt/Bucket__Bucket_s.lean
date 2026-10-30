module
public import Spec.go_etcd_io.bbolt.Bucket__Bucket_w
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

/-- `b.Bucket(name)` (`Bucket.Bucket.wspec`) with the transaction's shape: a bucket it opens
takes its entry's tree's tokens, and is that entry's (`bktNested`). -/
abbrev Bucket.Bucket.sspec : Prop :=
  ∀ (γ : GName) (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (name : GoSlice) (nb : List w8)
    (dk : DFrac),
  (T.bs !! bl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ txShape γ W T ∗
      name ↦*{dk} nb }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Bucket")) (Val #name))
  {{ (cl : Loc) (T' : WTx), RET #cl;
      ownWriteTx W txl T' ∗ txShape γ W T' ∗ ⌜wtxSub T T' ∧ (cl = null ∨ (T'.bs !! cl).isSome)⌝ ∗
      name ↦*{dk} nb }}

end spec

end bbolt
end EtcdGrove
end Perennial
