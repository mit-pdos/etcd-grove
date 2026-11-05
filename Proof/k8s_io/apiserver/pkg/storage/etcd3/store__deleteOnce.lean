/-
Lean-first (no Rocq counterpart).

The proof of `(*store).deleteOnce`: the caller's updates and token give the client's for the
conditional delete (`k8sAusRW_kvAu1`, by `delStepOk`: the store's history says a key-value at
`origState`'s mod revision is the one read); then the client's outcome: an error, success (the
object decoded into `out` at the new revision, the model's answer by `delete_at`), or a conflict
(nothing changed: the store's reading of the key at that state, `stateFromEtcdResponse`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__deleteOnce
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__stateFromEtcdResponse
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.txnError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest
public import Spec.k8s_io.klog.v2.V
public import Spec.k8s_io.klog.v2.Verbose__Infof
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__OptimisticDelete
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.deleteOnce.wp_proof
    (wp_stateFrom : store.stateFromEtcdResponse.spec (GF := GF) (hG := hG))
    (wp_txnError : txnError.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdRequest : metrics.RecordEtcdRequest.spec (GF := GF) (hG := hG))
    (wp_V : klog.V.spec (GF := GF) (hG := hG))
    (wp_Infof : klog.Verbose.Infof.spec (GF := GF) (hG := hG))
    (wp_kDel : kubernetes.Client.OptimisticDelete.spec (GF := GF) (hG := hG)) :
    store.deleteOnce.spec (GF := GF) (hG := hG) := by
  -- Stage 7b: restated at the Draft; the proof (at a93fbf6a24, before the restatement) is
  -- adapted in the Prove phase, after the Freeze: the origin state from `stFrom` (`stFrom_item`) in place of the read's key-value, and `pre`.
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
