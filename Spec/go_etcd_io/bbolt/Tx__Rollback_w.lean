module
public import Spec.go_etcd_io.bbolt.Tx__nonPhysicalRollback_w

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

/-- `tx.Rollback()` of the writer `txl` (not managed: inside `Update` it panics): its freelist
rolled back and the writer closed (`Tx.nonPhysicalRollback.wspec`). -/
abbrev Tx.Rollback.wspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (txid : w64) (σ : DBState)
    (T : WTx),
  I.RollbackSpec → I.IfaceFreeCountSpec → I.PendingCountSpec → I.EstimatedWritePageSizeSpec →
  T.t.writable' = true → T.t.managed' = false → T.t.db' = W.dbl →
  (T.bs !! structFieldRef Tx go!"root" txl).isSome → T.mv.txid' = txid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbWR I γ W txl txid σ ∗
      ownWriteTxG W txl T ∗ wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"Rollback")) (Val #()))
  {{ RET #interface.nil; ∃ (w : Reader) (t : Tx), ⌜σ.wr = some w⌝ ∗
      ownDB I W.dbl γ ({ σ with fl := σ.fl.rollback txid }.removeWriter w) ∗ txl ↦ t ∗
      ⌜t.db' = null⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
