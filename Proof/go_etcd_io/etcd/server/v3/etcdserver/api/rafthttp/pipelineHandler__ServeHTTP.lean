/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/pipelineHandler__ServeHTTP.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipelineHandler__ServeHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkClusterCompatibilityFromHeader
public import Spec.go_etcd_io.etcd.pkg.v3.ioutil.NewLimitedBufferReader
public import Spec.google_golang_org.protobuf.proto.UnmarshalPb
public import Spec.errors.AsLeaf
public import Spec.context.TODO
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
variable [ErrorStringNotWriter] [ErrorStringLeaf]

/-- `context.TODO()`'s `Done()` is `nil` (as `mvcc`'s `wp_todoCtx_Done`, for `todoCtx`). -/
theorem wp_todoCtx_Done' :
    {{ (True : IProp GF) }}
      (App (Val #(methods context.todoCtx.ty go!"Done" #(zero_val context.todoCtx))) (Val #()))
    {{ RET #chan.nil; True }} := by
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

theorem rafthttp.pipelineHandler.ServeHTTP.wp_proof
    (hRespHeader : ∀ H : http.HttpNet GF, http.RespHeader_spec H)
    (hHeaderSet : http.HeaderSet_spec (GF := GF))
    (hError : ∀ H : http.HttpNet GF, http.Error_spec H)
    (hWriteHeader : ∀ H : http.HttpNet GF, http.respWriteHeader_spec H)
    (hFlush : ∀ H : http.HttpNet GF, http.Flush_spec H)
    (hBodyRead : http.bodyRead_spec (GF := GF))
    (hReadAll : http.ReadAll_spec (GF := GF))
    (hCheck : rafthttp.checkClusterCompatibilityFromHeader.spec (GF := GF) (hG := hG))
    (hLimited : ioutil.NewLimitedBufferReader.spec (GF := GF) (hG := hG))
    (hUnmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG))
    (hAs : errors.AsLeaf.spec (GF := GF) (hG := hG))
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hGetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (hAsT : errors.AsTarget rafthttp.writerToResponse.ty) :
    rafthttp.pipelineHandler.ServeHTTP.spec (GF := GF) (hG := hG) := by
  intro Rh a γd Rs h wi r R γk rd Hhost Hpath
  iintro #Hpkg #Hh #HR #Hreq Htk Hbody Hw %hfl HRs
  iunfold pipeHandlerOk at Hh
  icases Hh with ⟨%hv, #Hhv, %Hhvok, #Hraft, #Haddr⟩
  rw [method_unfold (t := go.GoType.PointerType rafthttp.pipelineHandler.ty) (m := go!"ServeHTTP")]
  wp_pures
  ihave #HR0 := HR
  iunfold http.reqAt at HR
  icases HR with ⟨#HMeth, ⟨%u, #HU, #HUP⟩, ⟨%hm, #HHm, #Hhs⟩, ⟨%ra, #HRA, %Hra⟩, #HB, %Hrdnn⟩
  iStructNamed Hhv
  wp_auto
  wp_if_destruct
  · -- a `POST`: `w.Header().Set("X-Etcd-Cluster-ID", h.cid.String())`
    wp_apply hIDStringPtr _ DFrac.discard hv.cid' $$ [$cid] as %cs ⟨-, %_⟩
    wp_apply hRespHeader (raftHttpNet Rh) _ wi a R γk none [] rfl $$ [$Hw] as %hm' ⟨Hw, %hs', Hhm'⟩
    wp_apply hHeaderSet hm' hs' $$ [$Hhm'] as Hhm'
    -- the header check
    wp_apply hCheck hv.lg' hv.localID' hv.cid' hm R.hdr Hhvok.1 $$ [$Hhs] as %rv Hrv
    ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hri with ⟨-, -, -, #HIV, #HCM, #HES, -, ⟨%vRB, #HRB, %HRBl⟩, ⟨%vRF, #HRF, %HRFl⟩, -, -⟩
    icases Hrv with (%Hrv | ⟨%e, %Hre, #He⟩)
    · rcases Hrv with rfl | ⟨p, rfl⟩
      · -- `nil`: `addRemoteFromRequest(h.tr, r)`, then the body, read whole
        wp_auto
        wp_apply Haddr $$ [$HR0]
        ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
        · iPkgInit
        ihave #Heof0 := io.eof_of_init $$ Hio
        iunfold errors.newVar at Heof0
        icases Heof0 with ⟨%xe, #Heof, -⟩
        ihave #Hpre := http.bodyReader_prefixOk hBodyRead rd R
          (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe) Hrdnn
        wp_apply hLimited rd (http.bodyReader rd R) R.body _ (W64 65536) (by decide) $$ [$Hpre]
          as %lr #Hlr
        wp_apply hReadAll lr (http.bodyReader rd R) R.body _ $$ [$Hlr $Hbody] as %sl %err Hres
        · unfold http.ioEOF; iexact Heof
        icases Hres with (%Herr | ⟨%Herr, Hsl⟩)
        · -- the read failed: `400`
          cases err with
          | nil => exact absurd rfl Herr
          | ok ei =>
          wp_auto
          wp_apply hIDStringPtr _ DFrac.discard hv.localID' $$ [$localID] as %ls ⟨-, %_⟩
          wp_apply hZString as %f1 -
          wp_apply hZError as %f2 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          (try wp_auto)
          wp_apply hWarn hv.lg' _ _ $$ []
          · iframe #; ipureintro; exact Hhvok.1
          wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw] as Hw
          · simp only [raftHttpNet]
            isplitr
            · imodintro; iapply raftProto_resp_of <;> decide
            · ipureintro; decide
          -- `recvFailures.WithLabelValues(r.RemoteAddr).Inc()`
          wp_apply wp_slice_literal (V := GoString) [ra]
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hlsl, -⟩
          (try wp_auto)
          wp_apply hWLV vRF _ [go!"From"] [ra] _ $$ [$Hlsl] as %c ⟨%ci, %Hci, #Hc, -⟩
          · iframe #
            ipureintro
            refine ⟨HRFl, by simp, fun v hv => ?_⟩
            simp only [List.mem_singleton] at hv
            subst hv; exact utf8Valid_of_ascii _ Hra
          subst Hci
          iunfold prometheus.counterSpec at Hc
          icases Hc with ⟨#HInc, -⟩
          wp_apply HInc
          iexact HRs
        · subst Herr
          -- the protocol: a `POST` to `/raft` carries a message
          ihave #Hpr : pipeReq Rh R γk $$ []
          · iapply raftProto_req_pipe $$ Hreq
            ipureintro; exact ⟨Hif, Hpath⟩
          iunfold pipeReq at Hpr
          icases Hpr with ⟨%st, %Hst, #HP, #Hdep⟩
          wp_auto
          -- `proto.Unmarshal(b, &m)`: the body is an encoding, so it decodes
          have hU := hUnmarshal pbMessage sl R.body (DFrac.own 1) m_ptr
          simp only [pbMessage_ty, pbMessage_blank, pbMessage_wire] at hU
          wp_apply hU $$ [$Hsl $m] as %uerr ⟨Hsl, %Hok, Hdec⟩
          have Hue : uerr = GoInterface.nil := Hok ⟨st, Hst.1⟩
          subst Hue
          ihave ⟨%m', Hm', %Hw'⟩ := Hdec $$ %rfl
          wp_auto
          -- `receivedBytes.WithLabelValues(types.ID(m.GetFrom()).String()).Add(float64(len(b)))`
          ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
          wp_apply hGetFrom.1 m_ptr _ _ _ m' $$ [$Hm'] as Hm'
          haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
          wp_apply hIDString m'.msg.From' as %fs %Hfs
          wp_apply wp_slice_literal (V := GoString) [fs]
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hlsl, -⟩
          wp_auto_lc 1
          wp_apply hWLV vRB _ [go!"From"] [fs] _ $$ [$Hlsl] as %c ⟨%ci, %Hci, #Hc, -⟩
          · iframe #
            ipureintro
            refine ⟨HRBl, by simp, fun v hv => ?_⟩
            simp only [List.mem_singleton] at hv
            subst hv; exact utf8Valid_of_ascii _ Hfs
          subst Hci
          iunfold prometheus.counterSpec at Hc
          icases Hc with ⟨-, #HAdd⟩
          ihave #HA := HAdd $$ %sl.len %Hsllen.2
          wp_apply HA
          -- `h.r.Process(context.TODO(), &m)`: the copy, with its bundle
          wp_apply hTODO
          iunfold netRaftOk at Hraft
          icases Hraft with ⟨%ri, %Hri, #HProc, -⟩
          rw [Hri]
          wp_auto
          -- the one-shot part, withdrawn with the request's ticket
          iapply wp_fupd
          imod pipe_withdraw Rh.γn.N γk st ⊤ (by simp) $$ Hdep Htk Hlc1 with HO
          ihave #Hctx : nodeCtx (GF := GF) todoCtxVal bgCd $$ []
          · iunfold nodeCtx
            ileft
            iunfold doneNilCtx
            imodintro
            iapply wp_todoCtx_Done'
          wp_apply HProc $$ %todoCtxVal %bgCd %m_ptr [$HRs HO Hm'] as %perr ⟨#Hperr, HRs⟩
          · iframe #
            iunfold netRecv
            iexists st, m'
            iframe Hm' HO HP
            isplitr
            · ipureintro
              refine ⟨pbMessage_wire_eq Hst.1 Hw', ?_, Hw'.1⟩
              rw [Hst.2.1, Hhost]; exact Hhvok.2
            iunfold netSnapRecv
            iintro %h; exact absurd h Hst.2.2.1
          iunfold nodeErr at Hperr
          icases Hperr with (%Hpn | #Hps | #Hpc)
          · -- `nil`: `204`
            subst Hpn
            wp_auto
            wp_apply hWriteHeader (raftHttpNet Rh) _ wi a R γk (W64 204) rfl $$ [$Hw] as Hw
            · simp only [raftHttpNet]
              isplitr
              · imodintro; iapply raftProto_resp_of <;> decide
              · ipureintro; decide
            imodintro
            iexact HRs
          · -- `ErrStopped`: not a `writerToResponse`; `500`, then a panic
            ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
            · iPkgInit
            ihave #Hrinit := go_etcd_io.raft.v3.isInitialized_access $$ Hpraft
            unfold go_etcd_io.raft.v3.isInitialized
            icases Hrinit with ⟨%e1, %e2, %e3, %e4, %e5, %_, %_, %_, %_, %_, #Hrinit⟩
            iNamed Hrinit
            iunfold errStopped at Hps
            icases Hps with ⟨#Hps, %Hpsn⟩
            iunfold EtcdGrove.errorsNewVar at ErrStoppedNew
            icases ErrStoppedNew with ⟨%xs, #Hxs, -⟩
            icombine Hps Hxs gives %Heq
            subst Heq
            simp only [interface.mkOk]
            wp_auto
            wp_apply hAs xs writerErr_ptr (zero_val _) hAsT (ErrorStringLeaf.leaf _)
              ErrorStringNotWriter.notIn $$ [$writerErr] as writerErr
            wp_apply hIDStringPtr _ DFrac.discard hv.localID' $$ [$localID] as %ls ⟨-, %_⟩
            wp_apply hZString as %f1 -
            wp_apply hZError as %f2 -
            wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
            isplitr
            · ipureintro; rfl
            iintro %fsl ⟨-, -⟩
            (try wp_auto)
            wp_apply hWarn hv.lg' _ _ $$ []
            · iframe #; ipureintro; exact Hhvok.1
            wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw] as Hw
            · simp only [raftHttpNet]
              isplitr
              · imodintro; iapply raftProto_resp_of <;> decide
              · ipureintro; decide
            -- `w.(http.Flusher).Flush()`, then `panic(err)`, which `Serve` recovers
            rw [ite_cond_eq_true _ _ (eq_true hfl)]
            wp_auto
            wp_apply hFlush (raftHttpNet Rh) _ wi a R γk _ _ rfl $$ [$Hw] as Hw
            wp_apply wp_panic
            imodintro
            iexact HRs
          · -- a context error: none, `TODO()`'s context is never done
            iunfold ctxErr at Hpc
            icases Hpc with ⟨-, #Hf, -, -⟩
            simp only [bgCd]
            iexfalso
            iexact Hf
      · -- a panic
        wp_auto
        iexact HRs
    · -- one of the check's two errors: `412`, its message
      subst Hre
      icases He with (#He | #He)
      · iunfold EtcdGrove.errorsNewVar at HIV
        icases HIV with ⟨%x, #Hx, #HErr⟩
        icombine He Hx gives %Heq
        subst Heq
        wp_auto
        wp_apply HErr
        wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw] as Hw
        · simp only [raftHttpNet]
          isplitr
          · imodintro; iapply raftProto_resp_of <;> decide
          · ipureintro; decide
        iexact HRs
      · iunfold EtcdGrove.errorsNewVar at HCM
        icases HCM with ⟨%x, #Hx, #HErr⟩
        icombine He Hx gives %Heq
        subst Heq
        wp_auto
        wp_apply HErr
        wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw] as Hw
        · simp only [raftHttpNet]
          isplitr
          · imodintro; iapply raftProto_resp_of <;> decide
          · ipureintro; decide
        iexact HRs
  -- not a `POST`: `w.Header().Set("Allow", "POST")`, `405`
  wp_apply hRespHeader (raftHttpNet Rh) _ wi a R γk none [] rfl $$ [$Hw] as %hm' ⟨Hw, %hs', Hhm'⟩
  wp_apply hHeaderSet hm' hs' $$ [$Hhm'] as Hhm'
  wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw] as Hw
  · simp only [raftHttpNet]
    isplitr
    · imodintro; iapply raftProto_resp_of <;> decide
    · ipureintro; decide
  iexact HRs

end proof

end EtcdGrove
end Perennial
