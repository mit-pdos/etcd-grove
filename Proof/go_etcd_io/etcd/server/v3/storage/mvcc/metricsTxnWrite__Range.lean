/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Range

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

theorem mvcc.metricsTxnWrite.Range.wp_proof
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG) := by
  intro mw s γ kind ctx cd todo key endk k e ro crev Z
  wp_start as ⟨Htx, #Hctx, #Hkey, #Hend⟩
  cases kind with
  | read log rev =>
    simp only [mvcc.isTxn, mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    (try wp_auto)
    -- `tw.TxnWrite.Range(...)`: `txnReadWrite`'s promoted `Range`, then `storeTxnRead`'s
    -- (`storeTxnCommon.Range` on its embedded field)
    wp_method_call; wp_call
    (try wp_auto)
    wp_method_call; wp_call
    (try wp_auto)
    wp_apply (hRange tr s trace ti rt γ log rev ctx cd todo key endk k e ro crev Z)
      $$ [$Hs $Htr $Hrd $Hidx $Hti $Hctx $Hkey $Hend $Hmu] as %r %err ⟨%Htodo, Hti, Hmu, Hrd, Hout⟩
    (try wp_auto)
    iapply HΦ
    isplitl []
    · ipureintro; exact Htodo
    iframe Hout
    iunfold mvcc.isTxnRead
    iexists trw, tr, trace, ti, rt, (ranges + W64 1)
    iframe
    iframe #
  | write ilog pend puts deletes putSize =>
    simp only [mvcc.isTxn, mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
    iunfold mvcc.isTxnWrite at Htx
    iNamed Htx
    (try wp_auto)
    -- `tw.TxnWrite.Range(...)`: `storeTxnWrite.Range`
    wp_apply (hRangeW tw s γ ilog pend ctx cd todo key endk k e ro crev Z)
      $$ [$Htw $Hctx $Hkey $Hend] as %r %err ⟨%Htodo, Htw, Hout⟩
    (try wp_auto)
    iapply HΦ
    isplitl []
    · ipureintro; exact Htodo
    iframe Hout
    iunfold mvcc.isTxnWrite
    iexists tw, (ranges + W64 1)
    iframe

end proof

end EtcdGrove
end Perennial
