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

/-- `tx.nonPhysicalRollback()` of the writer `txl` (its meta's txid `txid`): the freelist rolled
back for `txid` (the pages it freed allocated again, those it allocated dropped), and the writer
closed (`Tx.close.wspec`). -/
abbrev Tx.nonPhysicalRollback.wspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (txid : w64) (σ : DBState)
    (T : WTx),
  I.RollbackSpec → I.IfaceFreeCountSpec → I.PendingCountSpec → I.EstimatedWritePageSizeSpec →
  T.t.writable' = true → T.t.db' = W.dbl → (T.bs !! structFieldRef Tx go!"root" txl).isSome →
  T.mv.txid' = txid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbWR I γ W txl txid σ ∗
      ownWriteTxG W txl T ∗ wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"nonPhysicalRollback")) (Val #()))
  {{ RET #(); ∃ (w : Reader) (t : Tx), ⌜σ.wr = some w⌝ ∗
      ownDB I W.dbl γ ({ σ with fl := σ.fl.rollback txid }.removeWriter w) ∗ txl ↦ t ∗
      ⌜t.db' = null⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
