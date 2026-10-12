/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Range
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3backend.Range.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hRange : txn.Range.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Range.spec (GF := GF) (hG := hG) := by
  intro E p r rq o log
  wp_start as ⟨#Hb, Hpre⟩
  iunfold apply.rangePre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨%Hrq, #Hr, ⟨Hrd, Hsw, Hknown⟩, Hres⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, #Hkv, -⟩
  iStructNamed Hopts
  wp_auto
  wp_apply hTODO
  iunfold apply.isApplyKV at Hkv
  icases Hkv with ⟨#Hkv, -⟩
  obtain ⟨hr, hk, hlen, hsort, hok⟩ := Hrq
  wp_apply (txn.range_soleWriter_of hRange log hlen todoCtxVal mvcc.neverCd opts.Logger' opts.KV'
      E.s E.γ r o true) $$ [$Hrd $Hsw]
    as %resp %trace %err ⟨Hrd, Hsw, %Htr, Hout⟩
  · iframe #
    isplitr
    · iapply mvcc.txnCtx_todo
    ipureintro; exact ⟨Hlg, hsort, hok⟩
  iapply HΦ
  iunfold apply.rangePost
  iexists (.applied log false)
  isplitr
  · ipureintro
    unfold apply.chainStep apply.backendStep
    rw [hk]
  simp only [apply.rangeOutcomeIs, apply.Outcome.logAfter]
  iframe Hres Hout
  iunfold apply.kvOwn
  iframe

end proof

end EtcdGrove
end Perennial
