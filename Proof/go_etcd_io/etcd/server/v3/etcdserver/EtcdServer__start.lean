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
  intro s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N hN
  wp_start as Hb
  iNamed Hb
  irename Hcancel => Hcancel0
  ihave #Hfb' := Hfb
  icases Hfb' with ⟨%fv, #Hfv⟩
  ihave #Hfv' := Hfv
  iunfold srvFieldsBuilt at Hfv'
  icases Hfv' with ⟨#Hlgf, %Hlgn, -, -, -, -, -, -, #Hfcf, -, #Hclf, -, -, #Hmidf, -, -, -, -, -⟩
  wp_auto
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  icases Hsc with ⟨%sc0, Hsc⟩
  icases Hscu with ⟨%scu0, Hscu⟩
  wp_auto
  -- the snapshot defaults
  wp_join iprop(∃ n : w64, srvSnapCountAddr s ↦ n ∗ s_ptr ↦ s ∗ lg_ptr ↦ fv.lg) with [Hsc s lg]
    as ⟨%sc1, Hsc, s, lg⟩
  · wp_apply hZU as %f1 -
    wp_apply hZU as %f2 -
    start_info
    wp_join_done
  wp_join iprop(∃ n : w64, srvSnapCatchUpAddr s ↦ n ∗ s_ptr ↦ s ∗ lg_ptr ↦ fv.lg) with [Hscu s lg]
    as ⟨%scu1, Hscu, s, lg⟩
  · wp_apply hZU as %f1 -
    wp_apply hZU as %f2 -
    start_info
    simp only [DefaultSnapshotCatchUpEntries]
    wp_auto
    wp_join_done
  ipersist Hsc
  ipersist Hscu
  -- `s.w = wait.New()`
  wp_apply hWN ρ.ids (reqWaitR ρ.ids E) as %w ⟨%γw, %RD, #Hwait, HRD⟩
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
  imod start_bag (V := Unit) (fun _ => iprop(True)) _ stc γst (by trivial) $$ Hstc Hsto with #Hstb
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
  ihave #Hvi : iprop(∃ v : GoString, globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ v) $$ []
  · iapply isPkgInit_access $$ Hpver
  icases Hvi with ⟨%verv, #Hverv⟩
  ihave #Hpmem : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hmi : iprop(∃ gv : Loc,
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterVersionMetrics ↦□ gv) $$ []
  · iapply isPkgInit_access $$ Hpmem
  icases Hmi with ⟨%cvm, #Hcvm⟩
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
    wp_apply hRCID fv.cluster as %cid -
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
    wp_apply hVS cv2 $$ [] as %vs2 -
    · iframe #; ipureintro; exact Hcv2
    wp_apply hVC as %cvs2 -
    wp_apply wp_map_make1 (K := GoString) (V := GoString) as %lm Hlm
    wp_apply wp_mapInsert go.string lm _ go!"cluster_version" cvs2 $$ [$Hlm] as Hlm
    wp_apply hGW cvm lm as %g ⟨%gi, %Hg, #Hgset⟩
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
  icases replicate_take2 _ _ maxReaders_ge2 $$ Hwgs with ⟨Hwg1, Hwg2, Hwgs⟩
  -- the views `run` needs
  ihave #Hsrv : isServer s γ ci TM E { ρ with wait := γw } γr $$ []
  · iunfold isServer
    iframe Hci
    isplitr
    · iexists { fv with w := w }
      ihave #Hfv2 := Hfv
      iunfold srvFieldsBuilt at Hfv2
      icases Hfv2 with ⟨#F1, %F2, #F3, #F4, %F5, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13, #F14,
        #F15, #F16, #F17, #F18, #F19⟩
      iunfold srvFieldsAt
      iframe #
      isplitr
      · ipureintro; exact F2
      isplitr
      · iunfold waitInv
        iexists RD
        iexact Hwait
      ipureintro; exact F5
    iunfold srvAtomics
    iframe #
  ihave #Hpwait : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait $$ []
  · iPkgInit
  ihave #Hwt := isWaitTime_of_timeList hTLW hTLT tl (appliedAtLeast γr) $$ [$Hpwait $Htl]
  ihave #Hsa : isServerApplyAll s γr $$ []
  · iunfold isServerApplyAll
    iunfold srvApplyAllBuilt at Hsab
    icases Hsab with ⟨%msc, #Hmsc, #Hmscb⟩
    iexists _, msc, sc1
    iframe #
  icases Hrunb with ⟨%vr, #Hvr⟩
  iunfold srvRunBuilt at Hvr
  icases Hvr with ⟨#Herf, #Herb, #Hcpf, #Hcpo, #Hstf, #Hltg⟩
  ihave #Hrf : srvRunFieldsAt s γr γg γcx ⟨vr.errorc, stc, dch, cancel, vr.compactor, vr.stats, lcn⟩ $$ []
  · iunfold srvRunFieldsAt
    iframe #
    isplitr
    · iunfold isUnitBag; iexists γst; iexact Hstb
    iunfold context.cancelSpec
    iexact Hcancel
  -- the apply thread's resources
  iunfold applyBuilt at Happ
  icases Happ with ⟨%st₀, %a, %t, %f, Hth, %Hlo, Hbe, Hca, Halg, Hbm, ⟨%ua, #Hua, Hkv⟩, Hao, #Hlog,
    Hfs⟩
  ihave Hstart : applyStart s γ ci b E γr ai₀ c₀ x₀ γw $$ [Hth Hbe Hca Halg Hbm Hkv Hao Hfs Hwg1 HRD]
  · iunfold applyStart
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Halg Hbm Hao Hfs Hwg1 Hlog
    isplitr
    · ipureintro; exact Hlo
    iunfold srvApplyKV
    iexists ua
    isplitr
    · iexact Hua
    isplitl [Hkv]
    · iexact Hkv
    iexists w, RD
    isplitr
    · iexact Hw
    isplitr
    · iapply isWait_waitOk $$ Hwait
    iexact HRD
  -- `go s.run()`
  wp_apply wp_fork $$ [Hsnap Hloop Happly Hrdone Hcomm Hdc Hclose Hstart Hlr HWB]
  · wp_apply hRun s γ ci TM E { ρ with wait := γw } γr Er γn γg γcx γd
      ⟨vr.errorc, stc, dch, cancel, vr.compactor, vr.stats, lcn⟩ b ai₀ at₀ c₀ x₀ N hN
      $$ [Hsnap Hloop Happly Hrdone Hcomm Hdc Hclose Hstart Hlr HWB]
    · iunfold isServerRun
      iframe
      iframe #
      ipureintro
      exact HEr
    ipureintro; exact isPanic_intoVal ()
  -- the views
  icases Hreqb with ⟨%vq, #Hvq⟩
  iunfold srvReqBuilt at Hvq
  icases Hvq with ⟨#Q1, #Q2, #Q3, #Q4, #Q5, #Q6, #Q7, #Q8, #Q9, #Q10, #Q11, #Q12, #Q13, #Q14,
    #Q15, #Q16, #Q17, %Q18⟩
  ihave #Hreq : isServerReq s E { ρ with wait := γw } $$ []
  · iunfold isServerReq
    iexists { vq with w := w, done := dch }
    iunfold srvReqFieldsAt
    iframe #
    isplitr
    · iunfold waitInv
      iexists RD
      iexact Hwait
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
    ipureintro; exact Q18
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
    { ρ with wait := γw } γr $$ [$Hpkg $Hreq $Hrd]
  ihave #Hrr : isReadRaft (interface.mkOk (go.GoType.PointerType raftNode.ty) #(srvRAddr s)) γr
      Er.RQ $$ []
  · rw [← HEr.2]
    iapply isReadRaft_of_raftNode hRSt hRI Er γn (srvRAddr s) $$ [$Hpkg $Hrn]
  icases replicate_take1 _ _ (by have := maxReaders_ge2; omega) $$ Hlcslots with ⟨Hlc1, Hlcslots⟩
  iapply HΦ
  iexists γw
  iframe Hreq Hrd
  iunfold srvStarted
  iframe Hwg2 Hwgs HNR
  isplitr
  · iexists rd
    iframe Hread
    iapply Hrlp $$ Hrs Hrr
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
