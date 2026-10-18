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
  iframe HΦ HRD HR sws
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

set_option maxHeartbeats 0 in
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
  intro sws r L0 sent0
  wp_start as ⟨#Hsws, Hrt, Hprod, Hpool, Hres⟩
  ihave #Hsws' := Hsws
  iunfold v3rpc.swsIs at Hsws'
  icases Hsws' with ⟨%Hnn, #Flg, #Fcid, #Fmid, #Fmrb, #Fsg, #Fwa, #Fag, #Fst, #Fws, #Fctrl, #Fpm,
    #Fvm, #Ffm, #Fcc, #Hsrv, #Hstream, #Hspec, #Haux, #Hup, #Hwstream, #Hwch, #Hch, #Hchinv, #Hspsc, #Hcc,
    #Hmu, %Hγoc, #Hsp, #Hcq, %Hγoc2⟩
  ihave #Hstream' := Hstream
  iunfold v3rpc.srvStreamIs at Hstream'
  icases Hstream' with ⟨%si, %Hsi, #HRecv, #HSend, #HCtx, #Hctxis, #Hrunctx⟩
  iunfold v3rpc.upOk at Hup
  iunfold v3rpc.watchSrvOk at Hsrv
  icases Hsrv with ⟨#Hwsto, %Hγst, #Hrso, #Hauth, #Hvars, -⟩
  iunfold v3rpc.watchVars at Hvars
  icases Hvars with ⟨#Heof, #Hwpv⟩
  iunfold v3rpc.watchPkgVars at Hwpv
  icases Hwpv with ⟨#HeInv, #HeOld, #HeEmpty, #HeDenied, #HeEWR, #HeDup, #HmCompacted,
    #HmInv, #HmOld, #HmEmpty, #HmDenied, #HmWC, #HstreamF, #Hh1, #Hh2, #Hh3, #Hh4, #Htracer,
    #Hcanc, #Hguard⟩
  iunfold v3rpc.eofVar at Heof
  icases Heof with ⟨%eofE, #HeofG, %HeofL, #HeofM⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pmvcc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hmi : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pmvcc
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨%enx, #Henx⟩, -⟩
  iunfold v3rpc.recvRes at Hres
  icases Hres with ⟨HR, HRD⟩
  icases Htracer with ⟨%tr, #Htrg⟩
  iunfold errVarLeaf at HeEWR HeDup
  icases HeEWR with ⟨%eEWR, #HeEWRg, -, #HeEWRm⟩
  icases HeDup with ⟨%eDup, #HeDupg, -, #HeDupm⟩
  iunfold errVarLeaf at HeInv HeOld HeEmpty HeDenied
  icases HeInv with ⟨%aInv, #HaInvg, %HaInvL, -⟩
  icases HeOld with ⟨%aOld, #HaOldg, %HaOldL, -⟩
  icases HeEmpty with ⟨%aEmp, #HaEmpg, %HaEmpL, -⟩
  icases HeDenied with ⟨%aDen, #HaDeng, %HaDenL, -⟩
  iunfold v3rpc.msgErrVar at HmCompacted HmInv HmOld HmEmpty HmDenied HmWC
  icases HmCompacted with ⟨%eC, #HeCg, #HeCm⟩
  icases HmInv with ⟨%eInv, #HeInvg, #HeInvm⟩
  icases HmOld with ⟨%eOld, #HeOldg, #HeOldm⟩
  icases HmEmpty with ⟨%eEmp, #HeEmpg, #HeEmpm⟩
  icases HmDenied with ⟨%eDen, #HeDeng, #HeDenm⟩
  wp_auto
  ihave Hinv : iprop(∃ (L : List v3rpc.WatchReqM) (sent : List Loc),
      "Hrt" ∷ v3rpc.srvRecvTok (Req := v3rpc.pbWatchRequest) r.γs L ∗
      "Hprod" ∷ spscProducer r.γctrl sent ∗
      "Hpool" ∷ v3rpc.ansPool r.γa L.length) $$ [Hrt Hprod Hpool]
  · iexists L0, sent0; iframe
  wp_for Hinv
  rw [Hsi]
  wp_apply HRecv $$ Hrt as %req %err Hrr
  icases Hrr with (⟨%Herr, %m, Hreq, HUp, Hrt⟩ | ⟨#Heofi, %Hne, Hrt, #Hcl⟩ | ⟨%Hne, #Hse, Hrt⟩)
  · -- a request
    subst Herr
    imod v3rpc.ansPool_mint_snoc r.γa L m $$ Hpool with ⟨Hpool, Hans⟩
    wp_apply hIs (· = GoInterface.nil) (fun _ => False) GoInterface.nil (GoInterface.ok eofE)
      (fun tii h => by cases h; exact HeofL.1.1) (by intro ii tii h; cases h) $$ [] as %b -
    · iframe #
      isplitl
      · iintro !> %ii %h; cases h
      · ipureintro; rfl
    wp_if_destruct
    rotate_left
    · wp_for_post
      iapply HΦ
      isplitr
      · ipureintro; left; rfl
      iexists sent; iexact Hprod
    iunfold v3rpc.watchReqRecv at Hreq
    icases Hreq with ⟨%u, #Hu, Hm⟩
    rcases m with c | cid | _ | _
    · -- create
      ihave ⟨%Hok, Htok⟩ := Hup $$ HUp
      icases Htok with ⟨Htok, #Hsrd⟩
      obtain ⟨Hpkv, Hfrag, Hfil, Hwid0⟩ := Hok
      ihave ⟨Hrt, #Hat⟩ := v3rpc.srvRecvTok_upAtW r.γs L (.create c) $$ Hrt
      icases Hm with ⟨%cr, Hon, Hcr⟩
      iunfold v3rpc.oneofCreate at Hon
      icases Hon with ⟨%w, %Hu', #Hw⟩
      subst Hu'
      iunfold v3rpc.createReqOwn at Hcr
      icases Hcr with ⟨%Hcrn, %ks, %es, %fs, Hks, #Hksv, Hes, #Hesv, #Hsr, #Hpn, #Hfs, #Hfsv, #Hpkvf,
        #Hwid, #Hfragf⟩
      wp_auto
      rw [decide_eq_false Hcrn.1]
      wp_auto
      ihave %Hkl := ownSlice_len $$ Hksv
      -- the key: `[]byte{0}` for an empty one
      wp_join iprop(∃ ks' : GoSlice, creq_ptr ↦ cr ∗
          structFieldRef etcdserverpb.WatchCreateRequest go!"Key" cr ↦ ks' ∗
          ks' ↦*□ (if c.key = [] then [W8 0] else c.key)) with [Hks creq] as ⟨%ks', creq, Hks, #Hksv'⟩
      · wp_apply wp_slice_literal (l := [W8 0])
        isplitr
        · ipureintro; rfl
        iintro %ksl ⟨Hk0, -⟩
        imod ownSlice_persist $$ Hk0 with #Hk0
        wp_auto
        wp_join_done
        iexists _
        iframe creq Hks
        have he : c.key = [] := by
          apply List.eq_nil_of_length_eq_zero; rw [Hkl.1, Hif]; rfl
        simp only [he, ↓reduceIte]
        iexact Hk0
      · iexists ks
        iframe Hks creq
        have hne : c.key ≠ [] := by
          intro h; rw [h] at Hkl; apply Hif; simp at Hkl; word
        simp only [hne, ↓reduceIte]
        iexact Hksv
      wp_if_destruct
      · -- a negative start revision: the compacted response
        to_params
        wp_apply hRev r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo $$ [$HR] as %rv HR
        · iframe #
        wp_apply hHdr $$ [] as %h ⟨%t, %ld, #Hh⟩
        · iframe #
        err_msg eC HeCm
        create_refused msg
      -- the permission check
      have hsr0 : 0 ≤ sint.Z c.startRev := by
        have := Hif; simp only [show sint.Z (W64 0) = 0 from rfl] at this; omega
      wp_apply hPerm sws r cr ks' es (if c.key = [] then [W8 0] else c.key) c.rangeEnd
        (DFrac.own 1) (DFrac.own 1) $$ [$HRD $Hks $Hes] as %perr ⟨HRD, Hks, Hes, #Hperr⟩
      · iframe #
        ipureintro
        split
        · simp
        · exact Hcrn.2
      rcases perr with pi | _
      rotate_left
      · -- permitted
        wp_auto
        ihave %Hel := ownSlice_len $$ Hesv
        -- the range end: `nil` for an empty one
        wp_join iprop(∃ es1 : GoSlice,
            ⌜(c.rangeEnd = [] → es1 = slice.nil) ∧ (c.rangeEnd ≠ [] → es1 ≠ slice.nil)⌝ ∗
            creq_ptr ↦ cr ∗
            structFieldRef etcdserverpb.WatchCreateRequest go!"RangeEnd" cr ↦ es1 ∗ es1 ↦*□ c.rangeEnd)
          with [Hes creq] as ⟨%es1, %Hes1, creq, Hes, #Hesv1⟩
        · have he : c.rangeEnd = [] := by
            apply List.eq_nil_of_length_eq_zero; rw [Hel.1, Hif]; rfl
          iexists slice.nil
          isplitr
          · ipureintro; exact ⟨fun _ => rfl, fun h => absurd he h⟩
          iframe
          rw [he]
          iapply ownSlice_nil
        · iexists es
          isplitr
          · ipureintro
            constructor
            · intro h
              exfalso; apply Hif
              have h1 := Hel.1; rw [h] at h1
              simp only [List.length_nil] at h1
              have h2 := Hel.2
              unfold sint.nat at h1
              word
            · intro _ hnil; apply Hif; rw [hnil]; rfl
          iframe
          iframe #
        ihave %Hel1 := ownSlice_len $$ Hesv1
        -- the range end: `[]byte{}` (from the key on) for `"\x00"`
        wp_join iprop(∃ es2 : GoSlice,
            ⌜(c.rangeEnd = [] → es2 = slice.nil) ∧
              (c.rangeEnd ≠ [] → c.rangeEnd ≠ [W8 0] → es2 ≠ slice.nil)⌝ ∗
            creq_ptr ↦ cr ∗
            structFieldRef etcdserverpb.WatchCreateRequest go!"RangeEnd" cr ↦ es2 ∗
            es2 ↦*□ (if c.rangeEnd = [W8 0] then [] else c.rangeEnd))
          at next with [Hes creq] as ⟨%es2, %Hes2, creq, Hes, #Hesv2⟩
        · wp_if_destruct
          · have h0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es1.len) := by
              rw [Hif]; decide
            rw [if_pos h0]
            obtain ⟨b, hb⟩ : ∃ b, c.rangeEnd = [b] := by
              rcases hre : c.rangeEnd with _ | ⟨b, _ | ⟨b', t⟩⟩
              · rw [hre] at Hel1; simp at Hel1; rw [Hif] at Hel1; exact absurd Hel1.1 (by decide)
              · exact ⟨b, rfl⟩
              · exfalso; rw [hre, Hif] at Hel1
                have h1 : sint.nat (W64 1) = 1 := rfl
                simp only [List.length_cons] at Hel1; omega
            wp_apply wp_load_slice_index es1 (sint.Z (W64 0)) c.rangeEnd DFrac.discard b (by decide)
              $$ [Hesv1] as -
            · iframe #; ipureintro; rw [hb]; rfl
            wp_if_destruct
            · wp_apply wp_slice_literal (l := ([] : List w8))
              isplitr
              · ipureintro; rfl
              iintro %esl ⟨He0, -⟩
              imod ownSlice_persist $$ He0 with #He0
              wp_auto
              wp_join_done
              iexists _
              iframe creq Hes
              isplitr
              · ipureintro
                exact ⟨fun h => absurd (hb.symm.trans h) (by simp), fun _ h => absurd hb h⟩
              rw [hb, if_pos rfl]
              iexact He0
            · wp_join_done
              have hne : c.rangeEnd ≠ [W8 0] := by
                intro h; rw [hb] at h; simp at h; exact Hif h
              simp only [hne, ↓reduceIte]
              iexists es1
              isplitr
              · ipureintro; exact ⟨Hes1.1, fun h _ => Hes1.2 h⟩
              iframe
              iframe #
          · have hne : c.rangeEnd ≠ [W8 0] := by
              intro h; rw [h] at Hel1; apply Hif; simp at Hel1; word
            simp only [hne, ↓reduceIte]
            isplitr
            · itrivial
            iexists es1
            isplitr
            · ipureintro; exact ⟨Hes1.1, fun h _ => Hes1.2 h⟩
            iframe
            iframe #
        wp_apply hFil cr fs c.filters DFrac.discard $$ [] as %fsl ⟨-, %fl, Hfl, %Hflen⟩
        · iframe #
        have hfl : fl = [] := Hflen.2 Hfil
        subst hfl
        imod ownSlice_persist $$ Hfl with #Hfl
        wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
        iapply HCtx
        · itrivial
        iintro !> -
        wp_auto
        wp_apply wp_bytes_to_string ks' _ DFrac.discard $$ [] as -
        · iframe #
        wp_apply hAStr as %kv1 -
        wp_apply wp_bytes_to_string es2 _ DFrac.discard $$ [] as -
        · iframe #
        wp_apply hAStr as %kv2 -
        wp_apply hAI64 as %kv3 -
        wp_apply hABool as %kv4 -
        wp_apply hABool as %kv5 -
        wp_apply hABool as %kv6 -
        wp_apply wp_slice_literal (l := [kv1, kv2, kv3, kv4, kv5, kv6])
        isplitr
        · ipureintro; rfl
        iintro %kvsl -
        wp_auto
        wp_apply hWA as %opt -
        wp_apply wp_slice_literal (l := [opt])
        isplitr
        · ipureintro; rfl
        iintro %optsl -
        wp_auto
        wp_apply hStart tr r.ci r.cd _ _ $$ [] as %ctx' %sp ⟨⟨%vs, #Hctx', Hctxw⟩, -, -⟩
        · iframe #
          iunfold mvcc.txnCtx
          iright; iexact Hctxis
        ihave #Hctx'' := Hctxw $$ Hctxis
        to_params
        ihave Htok : (v3rpc.wParams r.srv).T $$ [Htok]
        · unfold v3rpc.wParams mvcc.storeWatchParams; iexact Htok
        wp_apply hWatch r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo ctx'
          { r.cd with Values := vs } c.watchId ks' es2 fsl (if c.key = [] then [W8 0] else c.key)
          (if c.rangeEnd = [W8 0] then [] else c.rangeEnd) [] c.startRev c.sr $$ [$HR $Htok]
          as %id' %werr ⟨Hwres, HR⟩
        · iframe #
          isplitl
          · iapply BigSepL.bigSepL_nil.2; iempintro
          isplitr
          · ipureintro; exact ⟨hsr0, Hwid0⟩
          unfold v3rpc.wParams mvcc.storeWatchParams; iexact Hsrd
        icases Hwres with (⟨%Hwe, %Hrng, %w, %lo, -, #HIWF, #Hia, Hit, ⟨%γc', #HOC, %Hrg⟩, #HWS⟩ |
          ⟨%Hid, Hwe⟩)
        have Hid : c.watchId ≠ W64 0 → id' = c.watchId := fun h => absurd Hwid0 h
        · -- registered
          subst Hwe
          wp_auto
          wp_apply sync.RWMutex.wp_Lock_guard (swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) $$ []
            as ⟨Hlk, HP⟩
          · iframe #
          iunfold v3rpc.swsMu at HP
          icases HP with ⟨%PM, %VM, %FM, HPm, HVm, HFm, %HVF⟩
          wp_join iprop(∃ PM' : GMap w64 Bool, ownMap r.pm (DFrac.own 1) PM' ∗ sws_ptr ↦ sws ∗
              id_ptr ↦ id' ∗ creq_ptr ↦ cr) at next with [HPm sws id creq]
              as ⟨%PM', HPm, sws, id, creq⟩
          · cases hpn : c.progressNotify
            · wp_auto
              wp_join_done
            · wp_auto
              wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty r.pm PM id' true)
                $$ [$HPm] as HPm
              wp_join_done
          rw [Hpkv]
          wp_auto
          rw [Hfrag]
          wp_auto
          wp_apply sync.RWMutex.wp_Unlock_guard (swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm)
            $$ [$Hlk HPm HVm HFm]
          · iframe #
            inext
            iunfold v3rpc.swsMu
            iexists PM', VM, FM
            iframe
            ipureintro; exact HVF
          to_params
          wp_apply hRev r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo $$ [$HR] as %rv HR
          · iframe #
          wp_apply hHdr $$ [] as %h ⟨%t, %ld, #Hh⟩
          · iframe #
          wp_auto_lc 4
          -- the channel's sent list, after the registration (unit W-K)
          -- the watcher's registration index on the channel (K1b), and a snapshot after it
          ihave #HIWF' := HIWF
          simp only [v3rpc.wParams, mvcc.storeWatchParams] at *
          iunfold mvcc.watcherIs at HIWF'
          icases HIWF' with ⟨%γw1, %C1, #Hm1, -, -, ⟨%nr, #Hra1⟩, -⟩
          icases HOC with ⟨%γw2, #Hm2, %Hwc2⟩
          ihave %Hag := mvcc.watcherMeta_agree _ _ _ _ $$ Hm1 Hm2
          subst Hag
          ihave #Hra : mvcc.chanRegAt r.γc w nr $$ []
          · iunfold mvcc.chanRegAt at Hra1
            iunfold mvcc.chanRegAt
            rw [← Hγoc2.1, Hrg, ← Hwc2]
            iexact Hra1
          imod mvcc.chan_sent_snapshot_reg r.srv.γ r.ch r.γc w nr $$ Hlc4 Hchinv Hra
            with ⟨%l0, #Hl0, %Hnl⟩
          irename «$r0» => Hwr
          ihave %Hwrn := typedPointsto_not_null _ _ _ $$ Hwr
          ipersist Hwr
          let m : v3rpc.WatchRespM := ⟨⟨r.srv.cid, r.srv.mid, rv, t, ld⟩, id', true, false, 0,
            [], false, [], none⟩
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
            iapply spsc_send_au r.γctrl r.ctrl _ _ sent «$r0_ptr» _ $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [Hprod Hans Hit]
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
                exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr ⟨rfl, hsr0, Hid⟩⟩
              simp only [v3rpc.ctrlWatcher, m, Bool.false_eq_true, ↓reduceIte]
              iexists w, (mvcc.watchRangeOf (if c.key = [] then [W8 0] else c.key)
                (if c.rangeEnd = [W8 0] then [] else c.rangeEnd) es2 c.startRev id'), fsl, lo
              isplitr
              · ipureintro
                unfold v3rpc.createRangeOk mvcc.watchRangeOf
                refine ⟨rfl, rfl, rfl, ?_⟩
                by_cases h1 : c.rangeEnd = []
                · simp only [h1, ↓reduceIte, Hes2.1 h1]
                · by_cases h2 : c.rangeEnd = [W8 0]
                  · simp only [h2, ↓reduceIte]
                    by_cases h3 : es2 = slice.nil <;> simp [h3]
                  · simp only [h1, h2, ↓reduceIte, Hes2.2 h1 h2]
              iframe HIWF
              iframe Hia Hit Hfl
              isplitr
              · iexact HWS
              iexists l0, nr
              isplitr
              · iapply (mvcc.chanSentLb_stream r.γo r.γc l0 Hγoc.2.2.1).1 $$ Hl0
              isplitr
              · iapply (mvcc.chanRegAt_stream r.γo r.γc w nr Hγoc2.1).1 $$ Hra
              ipureintro; exact Hnl
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
        · -- refused
          ihave ⟨%ei, %Hwei, #Heim⟩ : ∃ ei : GoInterfaceOk, ⌜werr = GoInterface.ok ei⌝ ∗ errMsgOk ei $$ [Hwe]
          · icases Hwe with #Hg
            icombine Hg HeEWRg gives %Heq
            iexists eEWR; iframe #; ipureintro; exact Heq
          subst Hwei
          wp_auto
          to_params
          wp_apply hRev r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo $$ [$HR] as %rv HR
          · iframe #
          wp_apply hHdr $$ [] as %h ⟨%t, %ld, #Hh⟩
          · iframe #
          wp_auto
          err_msg ei Heim
          create_refused msg
      -- not permitted: the denied response
      wp_auto
      wp_join iprop(∃ reason : GoString, cancelReason_ptr ↦ reason ∗ err_ptr ↦ GoInterface.ok pi ∗
          sws_ptr ↦ sws) at next with [cancelReason err sws] as ⟨%reason, cancelReason, err, sws⟩
      · wp_apply v3rpc.wp_Is_applyErr hIs (GoInterface.ok pi) aInv HaInvL $$ [] as %b1 -
        · iframe #
        wp_if_destruct
        · err_msg eInv HeInvm
          wp_auto
          wp_join_done
        wp_apply v3rpc.wp_Is_applyErr hIs (GoInterface.ok pi) aOld HaOldL $$ [] as %b2 -
        · iframe #
        wp_if_destruct
        · err_msg eOld HeOldm
          wp_auto
          wp_join_done
        wp_apply v3rpc.wp_Is_applyErr hIs (GoInterface.ok pi) aEmp HaEmpL $$ [] as %b3 -
        · iframe #
        wp_if_destruct
        · err_msg eEmp HeEmpm
          wp_auto
          wp_join_done
        wp_apply v3rpc.wp_Is_applyErr hIs (GoInterface.ok pi) aDen HaDenL $$ [] as %b4 -
        · iframe #
        cases b4
        · wp_auto
          wp_apply hZE as %fld -
          wp_apply wp_slice_literal (l := [fld])
          isplitr
          · ipureintro; rfl
          iintro %fsl -
          wp_auto
          wp_apply hZErr $$ []
          · iframe #
            ipureintro; exact Hnn.2
          err_msg eDen HeDenm
          wp_auto
          wp_join_done
        · wp_auto
          err_msg eDen HeDenm
          wp_auto
          wp_join_done
      to_params
      wp_apply hRev r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo $$ [$HR] as %rv HR
      · iframe #
      wp_apply hHdr $$ [] as %h ⟨%t, %ld, #Hh⟩
      · iframe #
      create_refused reason
    · -- cancel
      ihave ⟨Hrt, #Hat⟩ := v3rpc.srvRecvTok_upAtW r.γs L (.cancel cid) $$ Hrt
      icases Hm with ⟨%cr, %Hcrn, Hon, #Hcid⟩
      iunfold v3rpc.oneofCancel at Hon
      icases Hon with ⟨%w, %Hu', #Hw⟩
      subst Hu'
      wp_auto
      rw [decide_eq_false Hcrn]
      wp_auto
      wp_apply hCancel r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo $$ [] as %cerr Hcerr
      · iframe #
        iunfold mvcc.rsnFor
        iexists v3rpc.cancelQ r.γs
        iframe Hcq
        iintro !>
        iunfold v3rpc.cancelQ
        iexists _
        iexact Hat
      icases Hcerr with (%Hce | #Hce)
      · subst Hce
        wp_auto
        to_params
        wp_apply hRev r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo $$ [$HR] as %rv HR
        · iframe #
        wp_apply +noauto hHdr $$ [] as %h ⟨%t, %ld, #Hh⟩
        · iframe #
        wp_auto_lc 3
        irename «$r0» => Hwr
        ihave %Hwrn := typedPointsto_not_null _ _ _ $$ Hwr
        ipersist Hwr
        let m : v3rpc.WatchRespM := ⟨⟨r.srv.cid, r.srv.mid, rv, t, ld⟩, cid, false, true, 0,
          [], false, [], none⟩
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
          iapply spsc_send_au r.γctrl r.ctrl _ _ sent «$r0_ptr» _ $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [Hprod Hans]
          · iframe Hprod
            iunfold v3rpc.ctrlP
            iexists m
            iframe Hmsg
            isplitr
            · ipureintro; exact ⟨rfl, rfl, rfl⟩
            iunfold v3rpc.ctrlOk
            iexists L.length, (.cancel cid), r.γo, r.γa
            iframe Hat Haux Hans
            isplitr
            · ipureintro
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [v3rpc.ctrlWatcher]
            itrivial
          iintro !> Hprod
          wp_auto
          wp_apply sync.RWMutex.wp_Lock_guard (swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) $$ []
            as ⟨Hlk, HP⟩
          · iframe #
          iunfold v3rpc.swsMu at HP
          icases HP with ⟨%PM, %VM, %FM, HPm, HVm, HFm, %HVF⟩
          wp_apply (wp_mapDelete r.pm PM cid go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool)
            $$ [$HPm] as HPm
          wp_apply (wp_mapDelete r.vm VM cid go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool)
            $$ [$HVm] as HVm
          wp_apply (wp_mapDelete r.fm FM cid go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool)
            $$ [$HFm] as HFm
          wp_apply sync.RWMutex.wp_Unlock_guard (swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm)
            $$ [$Hlk HPm HVm HFm]
          · iframe #
            inext
            iunfold v3rpc.swsMu
            iexists _, _, _
            iframe
            ipureintro
            intro id
            constructor
            · by_cases h : id = cid
              · subst h; exact GMap.lookup_delete_eq _ _
              · rw [GMap.lookup_delete_ne _ (Ne.symm h)]; exact (HVF id).1
            · by_cases h : id = cid
              · subst h; exact GMap.lookup_delete_eq _ _
              · rw [GMap.lookup_delete_ne _ (Ne.symm h)]; exact (HVF id).2
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
      · -- no such watcher: nothing
        icombine Hce Henx gives %Heq
        subst Heq
        wp_auto
        recv_next
    · -- progress
      ihave ⟨Hrt, #Hat⟩ := v3rpc.srvRecvTok_upAtW r.γs L .progress $$ Hrt
      icases Hm with ⟨%cr, %Hcrn, Hon⟩
      iunfold v3rpc.oneofProgress at Hon
      icases Hon with ⟨%w, %Hu', #Hw⟩
      subst Hu'
      wp_auto
      rw [decide_eq_false Hcrn]
      wp_auto
      wp_apply sync.RWMutex.wp_Lock_guard (swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) $$ []
        as ⟨Hlk, HP⟩
      · iframe #
      to_params
      -- the stream's progress fact: this request (unit W-M2)
      ihave #Hpf : mvcc.progFact r.γo.prog $$ []
      · iunfold mvcc.progFact
        iexists (v3rpc.progQ r.γs)
        iframe Hsp
        iintro !>
        iunfold v3rpc.progQ
        iexists L.length
        iexact Hat
      wp_apply hRPA r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo $$ [$HR] as %b HR
      · iframe #
      wp_apply sync.RWMutex.wp_Unlock_guard (swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm)
        $$ [$Hlk $HP]
      recv_next
    · -- other: excluded (`watchReqOk`)
      ihave ⟨%Hok, -⟩ := Hup $$ HUp
      exact Hok.elim
  · -- io.EOF
    iunfold v3rpc.eofIs at Heofi
    icombine Heofi HeofG gives %Heq
    subst Heq
    wp_apply hIs (· = GoInterface.ok eofE) (fun _ => False) (GoInterface.ok eofE)
      (GoInterface.ok eofE) (fun tii h => by cases h; exact HeofL.1.1)
      (_root_.Perennial.errors.treeTyped_pointer eofE _ HeofL.1.1) $$ [] as %b -
    · iframe #
      isplitl
      · iapply _root_.Perennial.errors.errorIsTree_leaf eofE _ _ HeofL.1.2.1 HeofL.1.2.2
      · ipureintro; rfl
    wp_if_destruct
    rotate_left
    · recv_ret_nil
    wp_for_post
    iapply HΦ
    isplitr
    · ipureintro; right; exact HeofL.2
    iexists _; iexact Hprod
  · -- another error
    iunfold v3rpc.streamErr at Hse
    icases Hse with ⟨%Hty, #HseT⟩
    ihave ⟨%S, %M, #Ht, %HS⟩ := HseT $$ %(GoInterface.ok eofE)
    wp_apply hIs S M err (GoInterface.ok eofE) (fun tii h => by cases h; exact HeofL.1.1)
      (HS.2 (fun tii h => by cases h; exact HeofL.1.1)) $$ [] as %b -
    · iframe #; ipureintro; exact HS.1
    wp_if_destruct
    rotate_left
    · recv_ret_nil
    rcases err with ei | _
    · wp_auto
      wp_for_post
      iapply HΦ
      isplitr
      · ipureintro; right; exact Hty
      iexists _; iexact Hprod
    · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
