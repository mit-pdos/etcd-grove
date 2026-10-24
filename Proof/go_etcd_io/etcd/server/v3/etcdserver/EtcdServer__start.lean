/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__start.lean`. Lean-first (no Rocq
counterpart); see `InvStart.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.github_com.Masterminds.semver.v3.Version__String
public import Spec.go_etcd_io.etcd.api.v3.version.Cluster
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__With
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_etcd_io.etcd.pkg.v3.wait.New
public import Spec.go_etcd_io.etcd.pkg.v3.wait.NewTimeList
public import Spec.go_etcd_io.etcd.pkg.v3.wait.timeList__Wait
public import Spec.go_etcd_io.etcd.pkg.v3.wait.timeList__Trigger
public import Spec.go_etcd_io.etcd.pkg.v3.notify.NewNotifier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.NewRead
public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeListIfc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadRaft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Perennial.Proof.context
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.types
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- `lg.Info(msg, fields...)`: the fields' slice literal, then `Info` (`hInfo`, `Hlgn`). -/
local macro "start_info" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply hInfo _ _ _ $$ []
  · iframe #; ipureintro; exact Hlgn
  (try wp_auto)))

set_option maxHeartbeats 0 in
theorem EtcdServer.start.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZU : zap.Uint64.spec (GF := GF) (hG := hG))
    (hWN : wait.New.spec (GF := GF) (hG := hG))
    (hTL : wait.NewTimeList.spec (GF := GF) (hG := hG))
    (hTLW : wait.timeList.Wait.spec (GF := GF) (hG := hG))
    (hTLT : wait.timeList.Trigger.spec (GF := GF) (hG := hG))
    (hNR : read.NewRead.spec (GF := GF) (hG := hG))
    (hNN : notify.NewNotifier.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG))
    (hRCID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hVS : semver.Version.String.spec (GF := GF) (hG := hG))
    (hVC : version.Cluster.spec (GF := GF) (hG := hG))
    (hGW : prometheus.GaugeVec.With.spec (GF := GF) (hG := hG))
    (hRun : EtcdServer.run.spec (GF := GF) (hG := hG))
    (hAW : EtcdServer.ApplyWait.spec (GF := GF) (hG := hG))
    (hDone : EtcdServer.Done.spec (GF := GF) (hG := hG))
    (hStop : EtcdServer.Stopping.spec (GF := GF) (hG := hG))
    (hLC : EtcdServer.LeaderChanged.spec (GF := GF) (hG := hG))
    (hFC : EtcdServer.FirstCommitInTermNotify.spec (GF := GF) (hG := hG))
    (hNRID : EtcdServer.NextRequestID.spec (GF := GF) (hG := hG))
    (hRT : EtcdServer.RequestTimeout.spec (GF := GF) (hG := hG))
    (hAI : EtcdServer.AppliedIndex.spec (GF := GF) (hG := hG))
    (hRSt : raftNode.ReadState.spec (GF := GF) (hG := hG))
    (hRI : raftNode.ReadIndex.spec (GF := GF) (hG := hG)) :
    EtcdServer.start.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N Hrb Hai0
  wp_start as Hb
  iNamed Hb
  irename Hcancel => Hcancel0
  ihave #Hfb' := Hfb
  icases Hfb' with ⟨%fv, #Hfv⟩
  ihave #Hfv' := Hfv
  iunfold srvFieldsBuilt at Hfv'
  icases Hfv' with ⟨#Hlgf, %Hlgn, -, -, -, -, -, -, -, #Hfcf, -, #Hclf, -, -, -, #Hmidf, -, -, -, -, -⟩
  -- the cluster's id (the request path's view of the same `s.cluster`)
  ihave #Hreqb' := Hreqb
  icases Hreqb' with ⟨%vq0, #Hvq0⟩
  iunfold srvReqBuilt at Hvq0
  icases Hvq0 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #Hclq, -, #Hpq, -⟩
  icombine Hclf Hclq gives %Hcleq
  iunfold srvPeersOk at Hpq
  icases Hpq with ⟨#Hcidq, -, -⟩
  wp_auto
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  icases Hsc with ⟨%sc0, Hsc⟩
  icases Hscu with ⟨%scu0, Hscu, %Hscu0⟩
  wp_auto
  -- the snapshot defaults
  wp_join iprop(∃ n : w64, srvSnapCountAddr s ↦ n ∗ s_ptr ↦ s ∗ lg_ptr ↦ fv.lg) with [Hsc s lg]
    as ⟨%sc1, Hsc, s, lg⟩
  · wp_apply hZU as %f1 -
    wp_apply hZU as %f2 -
    start_info
    wp_join_done
  wp_join iprop(∃ n : w64, srvSnapCatchUpAddr s ↦ n ∗ s_ptr ↦ s ∗ lg_ptr ↦ fv.lg ∗
      ⌜receiptBound GF ≤ uint.Z n + 1⌝) with [Hscu s lg]
    as ⟨%scu1, Hscu, s, lg, %Hscu1⟩
  · wp_apply hZU as %f1 -
    wp_apply hZU as %f2 -
    start_info
    simp only [DefaultSnapshotCatchUpEntries]
    wp_auto
    wp_join_done
    iexists _
    iframe
    ipureintro
    simpa using Hscu0
  · iexists _
    iframe
    ipureintro
    split at Hscu0
    · simp_all
    · exact Hscu0
  ipersist Hsc
  ipersist Hscu
  -- `s.w = wait.New()`
  wp_apply hWN ρ.ids (reqWaitR ρ E) as %w ⟨%γw, %RD, #Hwait, HRD⟩
  -- (linkv-txn stage B1) the member's registry, in the cluster's registries' map
  imod idWaitTok_set ρ.ids γw $$ Hwtok with #Hwn
  icases Hw with ⟨%w0, Hw⟩
  wp_auto
  -- `s.applyWait = wait.NewTimeList()`
  imod monoNatLbOwn_0 γr.applied with #H0
  ihave #Hmono : waitMono (appliedAtLeast (GF := GF) γr) $$ []
  · iunfold waitMono
    iintro !> %d %d' %Hle H
    iunfold appliedAtLeast at H
    iunfold appliedAtLeast
    iapply monoNatLbOwn_le _ (by word) $$ H
  wp_apply hTL (appliedAtLeast γr) $$ [] as %tl #Htl
  · iframe #
    iunfold appliedAtLeast
    rw [show uint.nat (W64 0) = 0 by word]
    iexact H0
  icases Haw with ⟨%aw0, Haw⟩
  wp_auto
  -- `s.done`, `s.stop`, `s.stopping`
  wp_apply chan.wp_make1 (V := Unit) as %dch %γd ⟨#Hdch, %Hdcap, Hdo⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γd dch $$ Hdch Hdo with Hdc
  icases Hdone with ⟨%d0, Hdone⟩
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %stc %γst ⟨#Hstc, %Hstcap, Hsto⟩
  -- `stop`: nothing is sent on it in the runs covered (no `Stop`/`HardStop`, D19m)
  imod start_bag (V := Unit) (fun _ => iprop(False)) _ stc γst (by trivial) $$ Hstc Hsto with #Hstb
  icases Hstop with ⟨%st0, Hstop⟩
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %sgc %γsg ⟨#Hsgc, %Hsgcap, Hsgo⟩
  · ipureintro; word
  imod alloc_stop_chan (E := ⊤) iprop(True) γsg sgc $$ Hsgc Hsgo with Hsg
  icases Hstopping with ⟨%sg0, Hstopping⟩
  wp_auto
  -- `s.ctx, s.cancel = context.WithCancel(context.Background())`
  ihave #Hpctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [] as %cctx %γcx %cancel
    ⟨#Hcancel, #Hcctx, #Hccc⟩
  · iframe #
  icases Hctx with ⟨%ctx0, Hctx⟩
  icases Hcancel0 with ⟨%cn0, Hcancel0⟩
  wp_auto
  ipersist Hw
  ipersist Haw
  ipersist Hdone
  ipersist Hstop
  ipersist Hstopping
  ipersist Hctx
  ipersist Hcancel0
  -- `s.read = read.NewRead(s, &s.r)`
  icases ownBroadcastChan_open _ _ _ _ $$ Hdc with ⟨%γdi, #Hdint, Hdtok⟩
  ihave #HdcU : ownBroadcastChan (GF := GF) dch γd iprop(True) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γdi; iframe #
  ihave Hdc := ownBroadcastChan_close _ _ _ .Pending γdi $$ [$Hdint $Hdtok]
  ihave #Hdok : srvDoneOk (GF := GF) (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) $$ []
  · iunfold srvDoneOk
    iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
    isplitr
    · ipureintro; rfl
    iunfold srvChanOk
    iintro !> %Φ' !> - HΦ'
    wp_apply hDone s dch $$ []
    · iframe #
    iapply HΦ'
    iunfold bcastChan
    iexists γd
    iexact HdcU
  icases Hnot with ⟨%x0, Hnot⟩
  ihave #Hprd : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
  · iPkgInit
  wp_apply hNR _ _ γr x0 $$ [Hnot] as %rd ⟨#Hisrd, #Hrlp, Hrslots⟩
  · iframe #; iframe Hnot
  icases Hread with ⟨%rd0, Hread⟩
  wp_auto
  ipersist Hread
  -- `s.leaderChanged = notify.NewNotifier()`
  ihave #Hpnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  wp_apply hNN as %lcn ⟨#Hlcn, Hlcslots⟩
  icases Hlc with ⟨%lc0, Hlc⟩
  wp_auto
  ipersist Hlc
  -- the start's log line (and the cluster version gauge, if the version is known)
  ihave #Hcv' := Hcv
  iunfold clusterVersionOk at Hcv'
  icases Hcv' with ⟨%γcv, #Hcvt⟩
  ihave #Hpver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Hvi : iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
      globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0") $$ []
  · iapply isPkgInit_access $$ Hpver
  icases Hvi with ⟨#Hverv, -⟩
  ihave #Hpmem : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hmi : iprop(∃ gv : Loc,
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterVersionMetrics ↦□ gv ∗
      ⌜prometheus.vecLabels gv [go!"cluster_version"]⌝) $$ []
  · iapply isPkgInit_access $$ Hpmem
  icases Hmi with ⟨%cvm, #Hcvm, %Hcvml⟩
  ihave #Hptypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hpsemver : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  ihave #Hpprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  wp_join at next with [s lg]
  · wp_bind (App (Val #(methods (go.GoType.PointerType EtcdServer.ty) go!"ClusterVersion" #s))
      (Val #()))
    iapply Hcvt $$ %false []
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    inext
    iintro %cv Hcvr
    wp_auto
    wp_if_destruct
    · -- not known: the log line without the cluster's id and version
      wp_apply hMID s fv.memberID $$ []
      · iframe #
      wp_apply hIDS as %ids1 -
      wp_apply hZS as %f0 -
      wp_apply hZS as %f1 -
      wp_apply hZS as %f2 -
      start_info
      wp_join_done
    -- known: the log line with the cluster's id and version, and the gauge
    icases Hcvr with (%Hcv0 | ⟨-, #Hcvk⟩)
    · exact absurd Hcv0.1 Hif
    wp_apply hMID s fv.memberID $$ []
    · iframe #
    wp_apply hIDS as %ids1 -
    wp_apply hZS as %f0 -
    wp_apply hZS as %f1 -
    wp_apply hCl s fv.cluster $$ []
    · iframe #
    wp_apply hRCID fv.cluster vq0.cid $$ []
    · rw [Hcleq]; iframe #
    wp_apply hIDS as %ids2 -
    wp_apply hZS as %f2 -
    wp_bind (App (Val #(methods (go.GoType.PointerType EtcdServer.ty) go!"ClusterVersion" #s))
      (Val #()))
    iapply Hcvt $$ %true []
    · simp only [↓reduceIte]; iexact Hcvk
    inext
    iintro %cv1 Hcv1
    icases Hcv1 with (%Hcv1 | ⟨%Hcv1, -⟩)
    · exact absurd Hcv1.2 (by decide)
    wp_apply hVS cv1 $$ [] as %vs1 -
    · iframe #; ipureintro; exact Hcv1
    wp_apply hVC as %cvs1 -
    wp_apply hZS as %f3 -
    start_info
    wp_bind (App (Val #(methods (go.GoType.PointerType EtcdServer.ty) go!"ClusterVersion" #s))
      (Val #()))
    iapply Hcvt $$ %true []
    · simp only [↓reduceIte]; iexact Hcvk
    inext
    iintro %cv2 Hcv2
    icases Hcv2 with (%Hcv2 | ⟨%Hcv2, -⟩)
    · exact absurd Hcv2.2 (by decide)
    wp_apply hVS cv2 $$ [] as %vs2 %Hvs2
    · iframe #; ipureintro; exact Hcv2
    wp_apply hVC as %cvs2 %Hcvs2
    wp_apply wp_map_make1 (K := GoString) (V := GoString) as %lm Hlm
    wp_apply wp_mapInsert go.string lm _ go!"cluster_version" cvs2 $$ [$Hlm] as Hlm
    wp_apply hGW cvm lm [go!"cluster_version"] _ _ $$ [Hlm] as %g ⟨%gi, %Hg, #Hgset, -⟩
    · iframe #; iframe Hlm; ipureintro
      exact ⟨Hcvml, prometheus.labelMapOk_one _ _ (utf8Valid_of_ascii _ (Hcvs2 Hvs2))⟩
    subst Hg
    wp_auto
    wp_bind (App (Val #(methods gi.ty go!"Set" gi.v)) (Val #(W64 4607182418800017408)))
    iapply Hgset $$ %(W64 4607182418800017408) []
    · itrivial
    inext
    iintro -
    wp_auto
    wp_join_done
  -- `GoAttach`'s protocol
  icases ownStopChan_pending_unknown _ _ _ $$ Hsg with ⟨Hsg, #HsgU⟩
  imod goAttach_init s sgc γsg (GoInterface.ok cctx) fv.lg Hbound Hlgn $$ Hstopping Hsg Hwg HwgMu
    Hctx Hlgf with ⟨%γg, #Hgok, Hclose, Hwgs⟩
  icases replicate_take2 _ _ sync.actualMaxReaders_ge_2 $$ Hwgs with ⟨Hwg1, Hwg2, Hwgs⟩
  -- the views `run` needs
  ihave #Hsrv : isServer s γ ci TM E { ρ with wait := γw } γr $$ []
  · iunfold isServer
    iframe Hci
    isplitr
    · ipureintro; exact Hρrd
    isplitr
    · iexists { fv with w := w }
      ihave #Hfv2 := Hfv
      iunfold srvFieldsBuilt at Hfv2
      icases Hfv2 with ⟨#F1, %F2, #F3, #F4, %F5, %F5o, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13,
        #F14, #F15, #F16, #F17, #F18, #F19, #F20⟩
      iunfold srvFieldsAt
      iframe #
      isplitr
      · ipureintro; exact F2
      isplitr
      · iunfold waitInv
        isplitr
        · iexists RD
          have hwr : reqWaitR (GF := GF) { ρ with wait := γw } E = reqWaitR ρ E := rfl
          rw [hwr]
          iexact Hwait
        iexact Hwn
      first
        | (ipureintro; exact ⟨F5, F5o⟩)
        | (isplitr
           · ipureintro; exact F5
           ipureintro; exact F5o)
    isplitr
    · iunfold srvAtomics
      iframe #
    ihave #Hrb := Hreqb
    icases Hrb with ⟨%vq0, #Hvq0⟩
    iunfold srvReqBuilt at Hvq0
    icases Hvq0 with ⟨#G1, #G2, #G3, -⟩
    isplitr
    · iunfold srvGenAt
      iexists vq0.gen
      iframe G1 G2
    iexact G3
  ihave #Hpwait : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait $$ []
  · iPkgInit
  ihave #Hwt := isWaitTime_of_timeList hTLW hTLT tl (appliedAtLeast γr) $$ [$Hpwait $Htl]
  ihave #Hsa : isServerApplyAll s γr $$ []
  · iunfold isServerApplyAll
    iunfold srvApplyAllBuilt at Hsab
    icases Hsab with ⟨%msc, #Hmsc, #Hmscb, #Hinfl⟩
    iexists _, msc, sc1
    iframe #
    isplitr
    · iunfold stopChan
      iexists γsg
      iexact HsgU
    ipureintro; exact Hscu1
  icases Hrunb with ⟨%vr, #Hvr⟩
  iunfold srvRunBuilt at Hvr
  icases Hvr with ⟨#Herf, #Herb, #Hcpf, #Hcpo, #Hstf, #Hltg⟩
  ihave #Hrf : srvRunFieldsAt s γr γg γcx ⟨vr.errorc, stc, dch, cancel, vr.compactor, vr.stats, lcn⟩ $$ []
  · iunfold srvRunFieldsAt
    iframe #
    iunfold context.cancelSpec
    iexact Hcancel
  -- the apply thread's resources
  iunfold applyBuilt at Happ
  icases Happ with ⟨%st₀, %a, %t, %f, Hth, %Hlo, Hbe, Hca, Halg, Hbm, ⟨%ua, #Hua, Hkv⟩, HRA, Hao,
    #Hlog, Hkr, Hfs⟩
  ihave Hstart : applyStart s γ ci b E γr ai₀ c₀ x₀ γw $$ [Hth Hbe Hca Halg Hbm Hkv HRA Hao Hfs Hwg1 HRD Hkr]
  · iunfold applyStart
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Halg Hbm Hao Hfs Hwg1 Hlog Hkr
    isplitr
    · ipureintro; exact Hlo
    iunfold srvApplyKV
    iexists ua
    isplitr
    · iexact Hua
    isplitl [Hkv]
    · iexact Hkv
    isplitl [HRA]
    · iexact HRA
    iexists w, RD
    isplitr
    · iexact Hw
    isplitr
    · iapply isWait_waitOk $$ Hwait
    iexact HRD
  -- `go s.run()`, with the write budget backed by time receipts (D19b)
  imod srvWTPool_alloc E.γ N ⊤ Hrb $$ HWB with ⟨%γp, #HWB, #HWA0⟩
  wp_apply wp_fork $$ [Hsnap Hloop Hsend Happly Hrdone Hcomm Hdc Hclose Hstart Hlr]
  · wp_apply hRun s γ ci TM E { ρ with wait := γw } γr Er γn γg γcx γd
      ⟨vr.errorc, stc, dch, cancel, vr.compactor, vr.stats, lcn⟩ b ai₀ at₀ c₀ x₀
      $$ [Hsnap Hloop Hsend Happly Hrdone Hcomm Hdc Hclose Hstart Hlr]
    · iunfold isServerRun
      iframe
      iframe #
      isplitr
      · ipureintro; exact HEr
      iexists γp
      iframe HWB
      rw [Hai0]; iexact HWA0
    ipureintro; exact isPanic_intoVal ()
  -- the views
  icases Hreqb with ⟨%vq, #Hvq⟩
  iunfold srvReqBuilt at Hvq
  icases Hvq with ⟨#Q1, #Q2, #Q3, #Q4, #Q5, #Q6, #Q7, #Q8, #Q9, #Q10, #Q11, #Q12, #Q13, #Q14,
    #Q15, #Q16, #Q17, #Q18, %Q19⟩
  ihave #Hreq : isServerReq s E { ρ with wait := γw } $$ []
  · iunfold isServerReq
    iexists { vq with w := w, done := dch }
    iunfold srvReqFieldsAt
    iframe #
    isplitr
    · iunfold waitInv
      isplitr
      · iexists RD
        have hwr : reqWaitR (GF := GF) { ρ with wait := γw } E = reqWaitR ρ E := rfl
        rw [hwr]
        iexact Hwait
      iexact Hwn
    isplitr
    · iunfold srvDoneChan
      iexists γd
      iexact HdcU
    isplitr
    · iunfold srvIndexInvs
      iexists γr
      iframe #
    have hmint : srvMintInv (GF := GF) { ρ with wait := γw } = srvMintInv ρ := rfl
    rw [hmint]
    iframe #
    ipureintro; exact Q19
  icases Hrdb with ⟨%vd, #Hvd⟩
  iunfold srvReadBuilt at Hvd
  icases Hvd with ⟨#R1, #R2, #R3, #R4, #R5, #R6, #R7, #R8, #R9, %R10, #R11, #R12, #R13, #R14, #R15⟩
  let awi : GoInterface :=
    interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.timeList.ty) #tl
  ihave #Hrd : isServerRead s E γr $$ []
  · iunfold isServerRead
    iexists ({ vd with read := rd, aw := awi, lc := lcn, stopping := sgc } : ReadFields)
    iunfold srvReadFieldsAt
    iframe #
    isplitr
    · ipureintro; exact R10
    iunfold stopChan
    iexists γsg
    iexact HsgU
  -- what `Start`'s goroutines and the request path get
  ihave #Hrs := isReadServer_of_server hAW hDone hStop hLC hFC hNRID hRT hAI hLg s E
    { ρ with wait := γw } γr Hρrd $$ [$Hpkg $Hreq $Hrd]
  -- the minted contexts (2026-10-16, stage R7b): from the mint and raft's commit invariant
  ihave #Hmint : readCtxMinted (GF := GF) γr $$ []
  · ihave #Hkvi3 := Hkvi
    iunfold srvKVInvs at Hkvi3
    icases Hkvi3 with ⟨-, -, #Hli, -⟩
    ihave #Hq17 := Q17
    iunfold srvMintInv at Hq17
    icases Hq17 with ⟨-, #Hrf⟩
    iapply readCtxMinted_of_mint γr ρ.ids
    iframe Hli
    rw [show γr.raft = ρ.raft by subst Hρrd; rfl]
    iexact Hrf
  ihave #Hrr : isReadRaft (interface.mkOk (go.GoType.PointerType raftNode.ty) #(srvRAddr s)) γr
      Er.RQ $$ []
  · rw [← HEr.2]
    iapply isReadRaft_of_raftNode hRSt hRI Er γn (srvRAddr s) $$ [$Hpkg $Hrn]
  icases replicate_take1 _ _ (by have := sync.actualMaxReaders_ge_2; omega) $$ Hlcslots with ⟨Hlc1, Hlcslots⟩
  ihave #HWBx : iprop(∃ γp, srvWTPool (GF := GF) E.γ γp) $$ []
  · iexists γp; iexact HWB
  iapply HΦ
  iexists γw
  iframe Hreq Hrd HWBx
  iunfold srvStarted
  iframe Hwg2 Hwgs HNR
  isplitr
  · ipureintro; exact Hρrd
  isplitr
  · iexists rd
    iframe Hread
    iapply Hrlp $$ Hrs Hrr [] Hmint
    iunfold readCompose
    iintro !> %gs #Hgs
    ihave #Hkvi2 := Hkvi
    iunfold srvKVInvs at Hkvi2
    icases Hkvi2 with ⟨#HkvI, -⟩
    iapply kv_read_compose γr.raft γr.kv gs $$ HkvI Hgs
  isplitl [Hlrl Hlc1 Hfcr]
  · iunfold srvReadLR
    isplitl [Hlrl]
    · iexact Hlrl
    iframe Hfcr
    iexists lcn
    iframe Hlc Hlc1
  isplitl [Hrslots]
  · iapply replicate_map _ _ (srvReadAddr s ↦□ rd) $$ [$Hread $Hrslots]
    iintro ⟨#Hr, Hslot⟩
    iunfold srvReadReader
    iexists rd
    iframe Hr Hslot
  iapply replicate_map _ _ (srvLeaderChangedAddr s ↦□ lcn) $$ [$Hlc $Hlcslots]
  iintro ⟨#Hl, Hslot⟩
  iexists lcn
  iframe Hl Hslot

end proof

end EtcdGrove
end Perennial
