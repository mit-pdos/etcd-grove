/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart). (Strict M1, 2026-11-05: over
txn's restated `Range.spec`, at the writer's read update, `envAus`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Range
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3
open mvcc.api (MvccState)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3backend.Range.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hRange : txn.Range.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Range.spec (GF := GF) (hG := hG) := by
  intro E p r rq o log info
  wp_start as ⟨#Hb, Htt, Hpre⟩
  iunfold apply.applyTok at Htt
  icases Htt with Hmr
  iunfold apply.rangePre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨%Hrq, #Hr, ⟨⟨%c, Hw⟩, Hbk, Hlive, Hard⟩, Hres⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨#Hlg, #Hkv, -, #Haus, -⟩
  iunfold apply.envAus at Haus
  icases Haus with ⟨-, #HauR, -⟩
  iunfold apply.isApplyKV at Hkv
  icases Hkv with #Hkv
  ihave Hau := HauR $$ %log %c %(srvApi.wSt E.γs log c) Hw []
  · iintro Hw; iexact Hw
  iunfold srvApi.auRead at Hau
  iStructNamed Hopts
  wp_auto
  wp_apply hTODO
  obtain ⟨hr, hk, hlen, hsort⟩ := Hrq
  wp_apply (hRange todoCtxVal mvcc.neverCd true opts.Logger' opts.KV' E.γ r o true none false _)
      $$ [$Hkv $Hmr $Hr $Hau]
    as %resp %trace %err ⟨Hmr, %Htr, ⟨%te', Htrc⟩, -, %σ, ⟨%Hσ, Hw⟩, %Hreach, Hout, -, %Hnd⟩
  · isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply traceutil.ctxTraceIs_todo
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    isplitr
    · simp only [↓reduceIte]; iapply mvcc.neverDone_neverCd
    isplitr
    · ihave #Hlg' := zapLoggerOk_orNil _ $$ Hlg; iexact Hlg'
    ipureintro; exact hsort
  subst Hσ
  have h2 := txn.reach_len (srvApi.stAt log c) Hreach.1
  simp only [srvApi.stAt] at h2
  have hrev : (W64 ((srvApi.stAt log c).rev : Int) : w64) = W64 ((log.length : Int) - 1) := by
    simp only [srvApi.stAt, mvcc.api.MvccState.rev]; congr 1; omega
  have hcr : (srvApi.stAt log c).crev = c := rfl
  have hlg : (srvApi.stAt log c).log = log := rfl
  rw [hrev, hcr, hlg] at *
  iapply HΦ
  iunfold apply.applyTok
  iframe Hmr
  isplitr [Htrc]
  rotate_left
  · iunfold apply.traceRes; iright; iexists te'; iexact Htrc
  iapply apply.rangePost_backend
  iexists (.applied log false)
  isplitr
  · ipureintro
    unfold apply.chainStep apply.backendStep
    rw [hk]
  simp only [apply.rangeOutcomeIs, apply.Outcome.logAfter]
  iframe Hres
  isplitl [Hout]
  · iexists c; iframe Hout; ipureintro
    have := Hnd rfl
    simp only [srvApi.stAt, mvcc.api.MvccState.rev] at this
    rwa [show ((log.length - 1 : Nat) : Int) = (log.length : Int) - 1 by omega] at this
  iunfold apply.kvOwn
  iframe Hbk Hlive Hard
  iexists c; iexact Hw

end proof

end EtcdGrove
end Perennial
