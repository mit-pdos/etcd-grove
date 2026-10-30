/-
Proof of the spec of the same name (the watch slice's unit W-S). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__recvLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__isWatchPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__newResponseHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.FiltersFromRequest
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Watch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Cancel
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgressAll
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.attribute.String
public import Spec.go_opentelemetry_io.otel.attribute.Int64
public import Spec.go_opentelemetry_io.otel.attribute.Bool
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Error
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchLemmas
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

set_option hygiene false in
/-- The store's reader slot `HR` as the watch params' (`P.R`), for a call of the mvcc stream. -/
macro "to_params" : tactic => `(tactic| (
  ihave HR : (v3rpc.wParams r.srv).R $$ [HR]
  · unfold v3rpc.wParams mvcc.storeWatchParams; iexact HR))

set_option hygiene false in
/-- `e.Error()` of an error whose `Error()` returns (`errMsgOk e` as `Hm`), into `%msg`. -/
macro "err_msg" e:term:max Hm:ident : tactic => `(tactic| (
  wp_bind (App (Val #(methods ($e).ty go!"Error" ($e).v)) (Val #()))
  iunfold errMsgOk at $Hm:ident
  iapply $Hm:ident
  · itrivial
  iintro !> %msg -))

set_option hygiene false in
/-- The receive loop's next iteration: the invariant back (the request recorded, the control
stream's producer at its sends). -/
macro "recv_next" : tactic => `(tactic| (
  wp_for_post
  iframe HΦ HRD HR sws «$res0»
  iexists _, _
  iframe Hrt Hprod Hpool))

set_option hygiene false in
/-- The receive loop's return of `nil`. -/
macro "recv_ret_nil" : tactic => `(tactic| (
  wp_for_post
  iapply HΦ
  isplitr
  · ipureintro; left; rfl
  iexists _; iexact Hprod))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The receiver's token knows the request at each position it received. -/
theorem v3rpc.srvRecvTok_upAtW (γ : v3rpc.StreamNames) (L : List v3rpc.WatchReqM) (m : v3rpc.WatchReqM) :
    v3rpc.srvRecvTok (GF := GF) (Req := v3rpc.pbWatchRequest) γ (L ++ [m]) ⊢
      v3rpc.srvRecvTok (Req := v3rpc.pbWatchRequest) γ (L ++ [m]) ∗ v3rpc.upAtW γ L.length m := by
  unfold v3rpc.srvRecvTok v3rpc.upAtW monoListIdxOwn
  iintro ⟨H1, #H2⟩
  iframe H1 H2
  ipureintro
  simp

/-- The answer token of the request received at position `L.length`. -/
theorem v3rpc.ansPool_mint_snoc (γa : GName) (L : List v3rpc.WatchReqM) (m : v3rpc.WatchReqM) :
    v3rpc.ansPool (GF := GF) γa L.length ⊢
      |==> (v3rpc.ansPool γa (L ++ [m]).length ∗ v3rpc.ansTok γa L.length) := by
  rw [List.length_append, List.length_singleton]
  exact v3rpc.ansPool_mint γa L.length

/-- `errors.Is(err, target)` of an error the apply package describes (`applyErrIs`) and a
pointer-leaf target: some boolean. -/
theorem v3rpc.wp_Is_applyErr (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err : GoInterface)
    (e : GoInterfaceOk) (he : errLeaf e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ applyErrIs err }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #(GoInterface.ok e)))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hpkg, #Herr⟩ HΦ
  ihave #HIsT := applyErrIs_tree err $$ Herr
  ihave ⟨%S, %M, #Ht, %HS⟩ := HIsT $$ %(GoInterface.ok e)
  iapply hIs S M err (GoInterface.ok e) (fun tii h => by cases h; exact he.1)
    (HS.2 (fun tii h => by cases h; exact he.1))
  · iframe #; ipureintro; exact HS.1
  iintro !> %b -
  iapply HΦ
  itrivial

set_option hygiene false in
/-- A refused create's response (`Created` and `Canceled`, watch id `-1`, `CancelReason = msg`) sent on
`sws.ctrlStream`, or the return on `sws.closec`: after a negative start revision (the compacted
response), the watcher's creation refused and permission denied (`msg` the reason). -/
local macro "create_refused" msg:term:max : tactic => `(tactic| (
    wp_auto_lc 3
    irename «$r0» => Hwr
    ihave %Hwrn := typedPointsto_not_null _ _ _ $$ Hwr
    ipersist Hwr
    let m : v3rpc.WatchRespM := ⟨⟨r.srv.cid, r.srv.mid, rv, t, ld⟩, W64 (-1), true, true, 0,
      $msg, false, [], none⟩
    ihave #Hmsg : v3rpc.watchRespMsg «$r0_ptr» m $$ []
    · iapply v3rpc.ctrlMsg_intro
      isplitr
      · ipureintro; exact Hwrn
      isplitl
      · iexact Hwr
      iexact Hh
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `sws.ctrlStream <- wr`
      simp only [chan.blockingClausePre]
      iexists (Loc), inferInstance, inferInstance, inferInstance, inferInstance, r.ctrl,
        r.γctrl.chanName, «$r0_ptr»
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · iunfold isSpsc at Hspsc; icases Hspsc with ⟨$, -⟩
      iapply spsc_send_au r.γctrl r.ctrl _ _ sent «$r0_ptr» _ $$ Hspsc [$(frameH `Hlc1) $(frameH `Hlc2) $(frameH `Hlc3)] [Hprod Hans]
      · iframe Hprod
        iunfold v3rpc.ctrlP
        iexists m
        iframe Hmsg
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        iunfold v3rpc.ctrlOk
        iexists L.length, (.create c), r.γo, r.γa
        iframe Hat Haux Hans
        isplitr
        · ipureintro
          first
            | simp [v3rpc.ctrlAnswers, m]; done
            | exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
        simp only [v3rpc.ctrlWatcher, m, ↓reduceIte]
        itrivial
      iintro !> Hprod
      wp_auto
      recv_next
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-sws.closec`: return
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, r.cc, r.γcc
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hcc
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hcc
      iintro -
      wp_auto
      recv_ret_nil
    iapply BigAndL.bigAndL_nil.2
    itrivial
  ))

theorem v3rpc.serverWatchStream.recvLoop.wp_proof
    (hWatch : mvcc.watchStream.Watch.spec (GF := GF) (hG := hG))
    (hRev : mvcc.watchStream.Rev.spec (GF := GF) (hG := hG))
    (hCancel : mvcc.watchStream.Cancel.spec (GF := GF) (hG := hG))
    (hRPA : mvcc.watchStream.RequestProgressAll.spec (GF := GF) (hG := hG))
    (hPerm : v3rpc.serverWatchStream.isWatchPermitted.spec (GF := GF) (hG := hG))
    (hHdr : v3rpc.serverWatchStream.newResponseHeader.spec (GF := GF) (hG := hG))
    (hFil : v3rpc.FiltersFromRequest.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hStart : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWA : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hAStr : «attribute».String.spec (GF := GF) (hG := hG))
    (hAI64 : «attribute».Int64.spec (GF := GF) (hG := hG))
    (hABool : «attribute».Bool.spec (GF := GF) (hG := hG))
    (hZErr : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG)) :
    v3rpc.serverWatchStream.recvLoop.spec (GF := GF) (hG := hG) := by
  -- the proof before G2: `git show 8527537fba:Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/serverWatchStream__recvLoop.lean`
  sorry -- G2: re-prove after freeze

end proof

end EtcdGrove
end Perennial
