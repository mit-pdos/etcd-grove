/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart). (Strict M1, 2026-11-05: over
txn's restated `DeleteRange.spec`, its updates built by the server's builders, `envAus`, as
`Put`'s.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__DeleteRange
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVBuild
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
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

theorem apply.applierV3backend.DeleteRange.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hDel : txn.DeleteRange.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro E p r rq o log F Pre Q Post info
  wp_start as ⟨#Hb, Hpre, #HF, Htt⟩
  iunfold apply.applyTok at Htt
  icases Htt with Hmr
  iunfold apply.deletePre at Hpre
  icases Hpre with ⟨%Hrq, #Hcp, #Hr, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨⟨%c, Hw⟩, Hlive, Hard, Hres, %B, Hbk, Hhk, Htie, Hcs⟩
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu, HltL⟩
  iunfold EtcdGrove.lease.lessorUser at Hu
  icases Hu with ⟨Hown, Hrdo, Hrvk⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨#Hlg, #Hkv, -, #Haus, -⟩
  iunfold apply.envAus at Haus
  icases Haus with ⟨#HauB, -, #HauE, -, #Hfacts, #Hfloor⟩
  iunfold apply.isApplyKV at Hkv
  icases Hkv with #Hkv
  obtain ⟨hdel, hk, hlen⟩ := Hrq
  -- the writer's facts: its floor, its log's witness and reachability
  imod Hfloor $$ %log %c %F Hw HF with ⟨Hw, %HFl⟩
  imod Hfacts $$ %log %c Hw with ⟨Hw, -, #Hnx0, -, %Hreach⟩
  have h2 : 2 ≤ log.length := txn.reach_len (srvApi.stAt log c) Hreach.1
  have hstep : apply.backendStep rq log
      (.applied (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) o)) false) := by
    unfold apply.backendStep; rw [hk]; exact ⟨o, hdel, rfl⟩
  -- the delete's updates (either outcome of its range read)
  ihave Hau : txn.delAU E.γ o (mvcc.leaseItemsOf (mvcc.stateAfter log))
      (fun σ ok => iprop(⌜σ = srvApi.stAt log c⌝ ∗
        srvApi.wSt E.γs (mvcc.commitLog log (txn.delPend o σ ok)) c)) $$ [Hw]
  · unfold txn.delAU
    iapply (apply.beginAU_of_auBegin E.γ (srvApi.stAt log c))
    iapply HauB $$ %log %c %_ Hw
    iintro Hw
    isplitr
    · ipureintro; rfl
    iintro %ok
    iapply apply.commitAU_of_auEnd
    cases ok
    · simp only [txn.delPend, Bool.false_eq_true, ↓reduceIte]
      ihave Hnx : E.Nx (mvcc.commitLog log []) $$ []
      · unfold mvcc.commitLog; simp only [↓reduceIte]; iexact Hnx0
      ihave He := HauE $$ %log %c %_ Hw Hnx
      iapply apply.auEnd_wand $$ He
      iintro HY
      isplitr
      · ipureintro; first | rfl | trivial
      iexact HY
    · simp only [txn.delPend, ↓reduceIte, srvApi.stAt]
      ihave Hnx := apply.certPre_backend_applied E rq log _ false hstep $$ Hcp
      ihave He := HauE $$ %log %c %_ Hw Hnx
      iapply apply.auEnd_wand $$ He
      iintro HY
      isplitr
      · ipureintro; first | rfl | trivial
      iexact HY
  ihave Hkb : txn.kvBackend E.γ 1 B (E.Pk B) E.f $$ [Hbk Hhk]
  · iunfold txn.kvBackend; iframe Hbk Hhk
  ihave Hcs : txn.csA (E.Pk B) E.f Pre Q Post $$ [Hcs]
  · iunfold srvApi.csContractA at Hcs; iunfold txn.csA; iexact Hcs
  iStructNamed Hopts
  wp_auto
  wp_apply hTODO
  ihave #HlgN := zapLoggerOk_orNil _ $$ Hlg
  wp_apply (hDel todoCtxVal mvcc.neverCd true opts.Logger' opts.KV' E.γ r o 1 B (E.Pk B)
      Pre Q Post E.f none false L (mvcc.leaseItemsOf (mvcc.stateAfter log)) _)
      $$ [$Hkv $Hmr $Hr $Hown $HlgN $Hkb $Hcs $Hau]
    as %resp %trace %err ⟨Hmr, Hkb, %Htrn, HPost, ⟨%te', Htrc⟩, -, %σ₀, -, Hout⟩
  · isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply traceutil.ctxTraceIs_todo
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    simp only [↓reduceIte]; iapply mvcc.neverDone_neverCd
  iunfold txn.kvBackend at Hkb
  icases Hkb with ⟨Hbk, Hhk⟩
  iapply HΦ
  iunfold apply.applyTok
  iframe Hmr
  isplitr [Htrc]
  rotate_left
  · iunfold apply.traceRes; iright; iexists te'; iexact Htrc
  iapply apply.kvPostF_backend
  icases Hout with (⟨%Herr, ⟨%Hσ, Hw⟩, #Hresp, Hhdr, Hown⟩ | ⟨%Hnd, -⟩)
  · -- the delete committed
    subst Hσ
    simp only [txn.delPend, ↓reduceIte, srvApi.stAt] at *
    iexists (.applied (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) o)) false)
    isplitr
    · ipureintro
      unfold apply.chainStep
      exact ⟨hstep, fun _ _ _ => HFl⟩
    simp only [apply.deleteAnswerIs, apply.deleteOutcomeIs, apply.noSpaceErrIs, apply.Outcome.logAfter,
      Bool.false_eq_true, ↓reduceIte, apply.appliedHdr]
    iframe Hres Hresp Hhdr
    isplitl []
    · ipureintro; exact ⟨Herr, h2, by unfold apply.delOk at hlen; omega⟩
    isplitl [Hw Hbk Hhk Htie Hown Hrdo Hrvk Hard HltL]
    · iapply (apply.kvOwn_of_split E _ B c)
      iframe Hw Htie
      iunfold apply.kvRest
      iframe Hbk Hhk Hard
      iunfold apply.leasesLive
      iexists L
      isplitr [Hown Hrdo Hrvk HltL]
      · iapply apply.leasesKnown_commit_delete $$ Hknown
      iunfold EtcdGrove.lease.lessorUser
      rw [txn.stateAfter_commitLog]
      iframe Hown Hrdo Hrvk HltL
    ileft; iexact HPost
  · -- the range read's context error: not at `context.TODO()` (`nd`)
    simp at Hnd

end proof

end EtcdGrove
end Perennial
