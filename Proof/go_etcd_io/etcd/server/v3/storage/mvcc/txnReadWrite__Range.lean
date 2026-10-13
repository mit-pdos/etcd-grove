/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.txnReadWrite.Range.wp_proof
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.Range.spec (GF := GF) (hG := hG) := by
  intro trw s γ log rev ctx cd todo key endk k e ro crev Z
  wp_start as ⟨Hro, #Hctx, #Hk, #He⟩
  iunfold mvcc.isRoTxnWrite at Hro
  icases Hro with ⟨%mw, Hf, Htx⟩
  (try wp_auto)
  ihave Htx : mvcc.isTxn mw s γ (.read log rev) crev Z $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  wp_apply (hRange mw s γ (.read log rev) ctx cd todo key endk k e ro crev Z)
    $$ [$Hpkg $Htx $Hctx $Hk $He] as %r %err ⟨%Hr, Htx, Hout⟩
  (try wp_auto)
  simp only [mvcc.isTxn, mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
  iapply HΦ
  iframe Hout
  isplitl []
  · ipureintro; exact Hr
  iunfold mvcc.isRoTxnWrite
  iexists mw
  iframe

end proof

end EtcdGrove
end Perennial
