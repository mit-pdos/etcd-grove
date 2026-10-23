/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/pipeline__handle.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__handle
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__post
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__activate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__deactivate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isMsgApp
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isMsgSnap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats__Succ
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats__Fail
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage
public import Spec.google_golang_org.protobuf.proto.SizePb
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Perennial.Spec.time.Now
public import Perennial.Proof.time.PtrMethods
public import Perennial.Spec.sync.WaitGroup__Done

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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem rafthttp.pipeline.handle.wp_proof
    (hPost : rafthttp.pipeline.post.spec (GF := GF) (hG := hG))
    (hActivate : rafthttp.peerStatus.activate.spec (GF := GF) (hG := hG))
    (hDeactivate : rafthttp.peerStatus.deactivate.spec (GF := GF) (hG := hG))
    (hIsApp : rafthttp.isMsgApp.spec (GF := GF) (hG := hG))
    (hIsSnap : rafthttp.isMsgSnap.spec (GF := GF) (hG := hG))
    (hSucc : v2stats.FollowerStats.Succ.spec (GF := GF) (hG := hG))
    (hFail : v2stats.FollowerStats.Fail.spec (GF := GF) (hG := hG))
    (hMarshal : pbutil.MustMarshalMessage.spec (GF := GF) (hG := hG))
    (hSize : proto.SizePb.spec (GF := GF) (hG := hG))
    (hGetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Sub : time.Time.Sub.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG)) :
    rafthttp.pipeline.handle.spec (GF := GF) (hG := hG) := by
  intro Rh p to R
  wp_start as ⟨#Hh, HR, Hdone⟩
  ihave #Hh' := Hh
  iunfold pipeHandleOk at Hh'
  icases Hh' with ⟨#Hs, %ps, %fs, %r, %id, %γd, %mc, %γm, #Hps, #Hpsok, #Hfs, #Hr, #Hraft,
    #Hmc, #Hbag⟩
  ihave #Hs' := Hs
  iunfold pipeSenderOk at Hs'
  icases Hs' with ⟨%tr, %pk, %sc, %ec, %γs, %lg, %urls, %uvs, %lid, %cid, %rt, -, -, #Hsc, -,
    -, -, -, -, -, -, -, -, -, -, #Hstop, -⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, ⟨%vSB, #HSB, %HSBl⟩, ⟨%vSF, #HSF, %HSFl⟩, -⟩
  iunfold netRaftOk at Hraft
  icases Hraft with ⟨%ri, %Hri, -, -, #HRU, #HRS⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_for_core
  (try wp_auto)
  cleanup_bool_decide
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, mc, γm
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %ml Hm
    iunfold pipeMsg at Hm
    icases Hm with ⟨%st, #Hm, #HP, HO, %Hst⟩
    (try wp_auto)
    wp_apply wp_Now as %t0 -
    (try wp_auto)
    have wpM := hMarshal pbMessage ml st Hst.1
    simp only [pbMessage_ty, pbMessage_ro, pbMessage_wire] at wpM
    wp_apply wpM $$ [$Hm] as %d ⟨Hd, -, %Hw⟩
    (try wp_auto)
    wp_apply hPost Rh p to d _ st Hw Hst.2.1 Hst.2.2.1 Hst.2.2.2 $$ [$Hs $Hd $HP $HO] as %err #Herr
    (try wp_auto)
    wp_apply wp_Now as %t1 -
    (try wp_auto)
    subst Hri
    cases err with
    | ok ei =>
      -- the post failed
      iunfold http.errStrOk at Herr
      icases Herr with (%Hn | ⟨%ei', %He, #HE, -⟩)
      · cases Hn
      cases He
      wp_auto
      wp_apply HE as %es
      (try wp_auto)
      wp_apply hDeactivate ps _ es $$ [$Hpsok]
      (try wp_auto)
      wp_apply hIsApp ml st $$ [$Hm]
      wp_if_destruct
      all_goals (try wp_if_destruct)
      all_goals (try (wp_apply hFail fs $$ []; ipureintro; assumption))
      all_goals
        (try wp_auto)
        wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [$Hm] as -
        (try wp_auto)
        wp_apply HRU
        (try wp_auto)
        wp_apply hIsSnap ml st $$ [$Hm]
        rw [decide_eq_false Hst.2.2.1]
        (try wp_auto)
        wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [$Hm] as -
        (try wp_auto)
        haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
        (try wp_auto)
        wp_apply hIDString as %ts %Hts
        wp_apply wp_slice_literal (V := GoString) [ts]
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        (try wp_auto)
        wp_apply hWLV vSF _ [go!"To"] [ts] _ $$ [$Hlsl] as %c ⟨%ci, %Hci, #Hc, -⟩
        · iframe #
          ipureintro
          refine ⟨HSFl, by simp, fun v hv => ?_⟩
          simp only [List.mem_singleton] at hv
          subst hv; exact utf8Valid_of_ascii _ (Hts ▸ types.idStr_ascii _)
        subst Hci
        iunfold prometheus.counterSpec at Hc
        icases Hc with ⟨#HInc, -⟩
        wp_apply HInc
        (try wp_auto)
        wp_for_post
        iframe
    | nil =>
      -- the post succeeded
      wp_auto
      irename «end» => Hend
      wp_apply hActivate ps $$ [$Hpsok]
      (try wp_auto)
      wp_apply hIsApp ml st $$ [$Hm]
      wp_if_destruct
      all_goals (try wp_if_destruct)
      all_goals (try (
        wp_apply (time.Time.wp_ptr_Sub_of wp_Sub) $$ [$Hend] as %dd Hend
        (try wp_auto)
        wp_apply hSucc fs dd $$ []
        ipureintro; assumption))
      all_goals
        (try wp_auto)
        wp_apply hIsSnap ml st $$ [$Hm]
        rw [decide_eq_false Hst.2.2.1]
        (try wp_auto)
        have wpS := hSize pbMessage ml st
        simp only [pbMessage_ty, pbMessage_ro] at wpS
        wp_apply wpS $$ [$Hm] as %n ⟨%Hn, -⟩
        (try wp_auto)
        wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [$Hm] as -
        (try wp_auto)
        haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
        (try wp_auto)
        wp_apply hIDString as %ts %Hts
        wp_apply wp_slice_literal (V := GoString) [ts]
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        (try wp_auto)
        wp_apply hWLV vSB _ [go!"To"] [ts] _ $$ [$Hlsl] as %c ⟨%ci, %Hci, #Hc, -⟩
        · iframe #
          ipureintro
          refine ⟨HSBl, by simp, fun v hv => ?_⟩
          simp only [List.mem_singleton] at hv
          subst hv; exact utf8Valid_of_ascii _ (Hts ▸ types.idStr_ascii _)
        subst Hci
        iunfold prometheus.counterSpec at Hc
        icases Hc with ⟨-, #HAdd⟩
        have Hn0 : 0 ≤ sint.Z n := by rw [Hn]; omega
        ihave #HA := HAdd $$ %n %Hn0
        wp_apply HA
        (try wp_auto)
        wp_for_post
        iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hstop
    iapply broadcast_chan_receive $$ Hstop
    iintro -
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Done_of wp_Done R _) $$ [$HR $Hdone]
    (try wp_auto)
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
