module
public import Proof.go_etcd_io.bbolt.DBRollback
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

/-- `tx.close()` of the writer `txl` (its view `w`): the freelist's statistics read, `rwtx`
cleared and the write lock released, the statistics merged; the database without the writer
(its view's fractions back; the caller says its facts hold without it), the transaction's
references cleared. -/
abbrev Tx.close.wspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (txid : w64) (σ : DBState)
    (T : WTx) (w : Reader),
  I.IfaceFreeCountSpec → I.PendingCountSpec → I.EstimatedWritePageSizeSpec →
  σ.wr = some w → (∀ v0 v1 : internal.common.Meta, dbOK σ v0 v1 → dbOK (σ.removeWriter w) v0 v1) →
  T.t.writable' = true → T.t.db' = W.dbl → (T.bs !! structFieldRef Tx go!"root" txl).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbWR I γ W txl txid σ ∗
      ownWriteTxG W txl T ∗ wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"close")) (Val #()))
  {{ RET #(); ∃ (t : Tx), ownDB I W.dbl γ (σ.removeWriter w) ∗ txl ↦ t ∗ ⌜t.db' = null⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
