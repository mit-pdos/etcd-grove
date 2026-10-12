/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Range

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
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG) := by
  intro mw s γ log rev ctx cd key endk k e ro
  wp_start as ⟨Htx, #Hctx, #Hkey, #Hend⟩
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  (try wp_auto)
  -- `tw.TxnWrite.Range(...)`: `txnReadWrite`'s promoted `Range`, then `storeTxnRead`'s
  -- (`storeTxnCommon.Range` on its embedded field)
  wp_method_call; wp_call
  (try wp_auto)
  wp_method_call; wp_call
  (try wp_auto)
  wp_apply (hRange tr s trace ti rt γ log rev ctx cd key endk k e ro)
    $$ [$Hs $Htr $Hidx $Hti $Hctx $Hkey $Hend] as %r %err ⟨Hti, Hout⟩
  (try wp_auto)
  iapply HΦ
  iframe Hout
  iunfold mvcc.isTxnRead
  iexists trw, tr, trace, ti, rt, (ranges + W64 1)
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
