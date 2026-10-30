module
public import Proof.go_etcd_io.bbolt.DBLost
public import Proof.go_etcd_io.bbolt.WriteAlloc

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
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `tx.close()` of the writer `txl` of a database whose mapping was lost (`dbLost`, after a
failed remap): the freelist's statistics read, `rwtx` cleared and the write lock released, the
statistics merged, the transaction's references cleared. -/
abbrev Tx.close.lspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (W : WView) (txl : Loc) (txid : w64) (fl : FLState) (T : WTx),
  I.IfaceFreeCountSpec → I.PendingCountSpec → I.EstimatedWritePageSizeSpec →
  T.t.writable' = true → T.t.db' = W.dbl → (T.bs !! structFieldRef Tx go!"root" txl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbLost I W.dbl txl txid fl ∗
      ownWriteTxG W txl T }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"close")) (Val #()))
  {{ RET #(); ∃ (t : Tx), txl ↦ t ∗ ⌜t.db' = null⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
