/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__start.lean`. Lean-first (no Rocq
counterpart); see `InvStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.CtxLaws
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
import all Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  · iframe #
  (try wp_auto)))

set_option maxHeartbeats 0 in

/-- **`start.spec`**, in both auth modes (the auth component's 2c, 2026-11-04: one proof over the
component `C`; until then `wp_proofOff` and `wp_proofOn`, one per mode): the views at `C.isOn`,
the read side from the component's row (`acRes_read`), the compactor's run with auth off only
(`compactorRun`), `run` from `isServerRunC C`. -/
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
  intro s γ ci TM C E ρ γr Er γn b ai₀ at₀ c₀ x₀ N
  wp_start as ⟨%hC, Hb, #Hlnil⟩
  obtain ⟨hm, hRB, Hrb, Hai0⟩ := hC
  iNamed Hb
  irename Hcancel => Hcancel0
  ihave #Hfb' := Hfb
  icases Hfb' with ⟨%fv, #Hfv⟩
  ihave #Hfv' := Hfv
  iunfold srvFieldsBuilt at Hfv'
  icases Hfv' with ⟨#Hlgf, #Hlgn, -, -, -, -, -, #Hfcf, -, #Hclf, -, -, -, #Hmidf, -, -, -, -, -⟩
  -- the cluster's id (the request path's view of the same `s.cluster`)
  ihave #Hreqb' := Hreqb
  icases Hreqb' with ⟨%vq0, #Hvq0⟩
  iunfold srvReqBuiltM at Hvq0
  icases Hvq0 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #Hclq, -, #Hpq, -⟩
  icombine Hclf Hclq gives %Hcleq
  iunfold srvPeersOk at Hpq
  icases Hpq with ⟨#Hcidq, -, -⟩
  wp_auto
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe Hlgf; iframe Hlr Hlgn
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
  wp_apply hWN ρ.ids (reqWaitRM C.isOn ρ E) as %w ⟨%γw, %RD, #Hwait, HRD⟩
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
  · iframe Hmono
    iunfold appliedAtLeast
    rw [show uint.nat (W64 0) = 0 by word]
    iexact H0
  icases Haw with ⟨%aw0, Haw⟩
  wp_auto
  -- (R2c-4) the stop's: the configuration's data directory (the slot's), the right's claim
  iunfold srvStop.slot at Hskeep
  icases Hskeep with ⟨%cfgk, %γk, Hkeep, %hSTk⟩
  icases srvStop.dataDirField s cfgk E γn γk $$ Hkeep with ⟨#Hddf, Hkeep⟩
  imod token_alloc with ⟨%cs, Hcs⟩
  -- `s.done`, `s.stop`, `s.stopping`: `done`'s close announces the stopped server's image,
  -- escrowed for the claim (`srvDoneInv`; R2c-4: until then `True`)
  wp_apply chan.wp_make1 (V := Unit) as %dch %γd ⟨#Hdch, %Hdcap, Hdo⟩
  imod alloc_broadcast_chan (E := ⊤) (srvDoneInv ρ.rd.raft.raft ρ γn.id cfgk.DataDir' cs) γd dch
    $$ Hdch Hdo with Hdc
  icases Hdone with ⟨%d0, Hdone⟩
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %stc %γst ⟨#Hstc, %Hstcap, Hsto⟩
  -- `stop`: the stop requests (`srvStopReq`, what `HardStop` sends; R2c-4: until then `False`)
  imod start_bag (V := Unit) (fun _ => srvStopReq s E ρ cfgk.DataDir') _ stc γst (by trivial)
    $$ Hstc Hsto with #Hstb
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
  -- (R8, 2026-11-07) with its trace and span facts (`traceutil.wp_WithCancelBackground_noTrace`:
  -- the revocation's `LeaseRevoke` takes the span fact, `srvRevokeCtx`)
  wp_apply traceutil.wp_WithCancelBackground_noTrace $$ [] as %cctx %γcx %cancel
    ⟨#Hcancel, #Hcctx, -, #Hcspan, #Hcst, #Hclib⟩
  iunfold context.cancelSpec at Hcancel
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
  ihave #HdcU : ownBroadcastChan (GF := GF) dch γd
      (srvDoneInv ρ.rd.raft.raft ρ γn.id cfgk.DataDir' cs) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γdi; iframe Hdint
  ihave Hdc := ownBroadcastChan_close _ _ _ .Pending γdi $$ [$Hdint $Hdtok]
  -- (R2c-4) the right to stop the server: the channels, the claim, the data directory's field
  ihave Hright : iprop(∃ dd : GoString, srvStopRight (GF := GF) s E ρ.rd.raft.raft ρ γn.id dd)
      $$ [Hcs]
  · iexists cfgk.DataDir'
    iunfold srvStopRight
    iexists stc, dch, γst, γd, cs
    iframe Hcs
    iframe #
  -- the stop's slot, for `run`'s shutdown
  ihave Hskeep : srvStop.slot (GF := GF) s E γn Er $$ [Hkeep]
  · iunfold srvStop.slot
    iexists cfgk, γk
    iframe Hkeep
    ipureintro; exact hSTk
  ihave #Hdok : srvDoneOk (GF := GF) (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) $$ []
  · iunfold srvDoneOk
    iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
    isplitr
    · ipureintro; rfl
    iunfold srvChanOk
    iintro !> %Φ' !> - HΦ'
    wp_apply hDone s dch $$ []
    · iframe Hdone
    iapply HΦ'
    iexists _
    iunfold bcastChan
    iexists γd
    iexact HdcU
  icases Hnot with ⟨%x0, Hnot⟩
  ihave #Hprd : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
  · iPkgInit
  wp_apply hNR _ _ γr x0 (kvStM C.isOn γr.kv) $$ [Hnot] as %rd ⟨#Hisrd, #Hrlp, Hrslots⟩
  · iframe Hdok Hcci; iframe Hnot
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
  ihave #Hmi : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpmem
  icases Hmi with ⟨⟨%cvm, #Hcvm, %Hcvml⟩, -⟩
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
      · iframe Hmidf
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
    · iframe Hmidf
    wp_apply hIDS as %ids1 -
    wp_apply hZS as %f0 -
    wp_apply hZS as %f1 -
    wp_apply hCl s fv.cluster $$ []
    · iframe Hclf
    wp_apply hRCID fv.cluster vq0.cid $$ []
    · rw [Hcleq]; iframe Hcidq
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
    · ipureintro; exact Hcv1
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
    · ipureintro; exact Hcv2
    wp_apply hVC as %cvs2 %Hcvs2
    wp_apply wp_map_make1 (K := GoString) (V := GoString) as %lm Hlm
    wp_apply wp_mapInsert go.string lm _ go!"cluster_version" cvs2 $$ [$Hlm] as Hlm
    wp_apply hGW cvm lm [go!"cluster_version"] _ _ $$ [Hlm] as %g ⟨%gi, %Hg, #Hgset, -⟩
    · iframe Hlm; ipureintro
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
  ihave #HrP := srvRevokeBuilt_raftPool s E $$ Hrvkb
  imod goAttach_init s sgc γsg (GoInterface.ok cctx) fv.lg
    (by unfold backend.rdPoolN at Hbound; omega) $$ Hstopping Hsg Hwg HwgMu
    Hctx Hlgf Hlgn HrP with ⟨%γg, #Hgok, Hclose, Hwgs⟩
  icases replicate_take2 _ _ sync.actualMaxReaders_ge_2 $$ Hwgs with ⟨Hwg1, Hwg2, Hwgs⟩
  -- (revoke-open, 2026-11-06) the outer pool's `wgMu` slots
  icases replicate_takeN _ srvRevokePoolN _ (by
      unfold srvRevokePoolN backend.rdPoolN; rw [sync.rwmutex.actualMaxReaders_unseal]; decide)
    $$ Hwgs with ⟨HwgB, Hwgs⟩
  ihave Hwg1 : srvWgReader s $$ [Hwg1]
  · iunfold srvWgReader; iexists γg; iexact Hwg1
  ihave Hwgs := replicate_map _ (srvWgReader s) (srvGoAttachOk s γg) _ $$ [$Hgok $Hwgs]
  · iintro ⟨-, Hslot⟩
    iunfold srvWgReader
    iexists γg
    iexact Hslot
  -- the views `run` needs
  ihave #HkviM := (srvKVInvsM_C (GF := GF) C s E γr).2 $$ Hkvi
  ihave #Hsrv : isServerC C s γ ci TM E { ρ with wait := γw } γr $$ []
  · iunfold isServerC
    iframe Hci
    isplitr
    · ipureintro; exact Hρrd
    isplitr
    · iexists { fv with w := w }
      ihave #Hfv2 := Hfv
      iunfold srvFieldsBuilt at Hfv2
      icases Hfv2 with ⟨#F1, #F2, %F5, %F5o, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13,
        #F14, #F15, #F16, #F17, #F18, #F19, #F20⟩
      iunfold srvFieldsAtM
      iframe F20 F19 F18 F17 F16 F15 F14 F13 F12 F11 F10 F9 F8 F7 F6 F1 Hw
      isplitr
      · iexact F2
      isplitr
      · iunfold waitInvM
        isplitr
        · iexists RD
          have hwr : reqWaitRM (GF := GF) C.isOn { ρ with wait := γw } E = reqWaitRM C.isOn ρ E := rfl
          rw [hwr]
          iexact Hwait
        iexact Hwn
      first
        | (ipureintro; exact ⟨F5, F5o⟩)
        | (isplitr
           · ipureintro; exact F5
           ipureintro; exact F5o)
    isplitr
    · iunfold srvAtomicsC
      iframe Hti Hkvi Hai
    ihave #Hrb := Hreqb
    icases Hrb with ⟨%vq0, #Hvq0⟩
    iunfold srvReqBuiltM at Hvq0
    icases Hvq0 with ⟨#G1, #G2, #G3, -⟩
    isplitr
    · iunfold srvGenAt
      iexists vq0.gen
      iframe G1 G2
    iframe G3
    ipureintro; exact Hbound
  ihave #Hpwait : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait $$ []
  · iPkgInit
  ihave #Hwt := isWaitTime_of_timeList hTLW hTLT tl (appliedAtLeast γr) $$ [$Hpwait $Htl]
  ihave #Hsa : isServerApplyAll s γr $$ []
  · iunfold isServerApplyAll
    iunfold srvApplyAllBuilt at Hsab
    icases Hsab with ⟨%msc, #Hmsc, #Hmscb, #Hinfl, #Htrb, %Hkv0⟩
    iexists _, msc, sc1
    iframe #
    isplitr
    · iunfold stopChan
      iexists γsg
      iexact HsgU
    ipureintro; exact Hkv0
  icases Hrunb with ⟨%vr, #Hvr⟩
  iunfold srvRunBuilt at Hvr
  icases Hvr with ⟨#Herf, #Herb, #Hcpf, #Hcpo, #Hstf, #Hltg⟩
  ihave #Hrf : srvRunFieldsAt s γr γg γcx ⟨vr.errorc, stc, dch, cancel, vr.compactor, vr.stats, lcn⟩
      (srvStopReq s E ρ cfgk.DataDir') $$ []
  · iunfold srvRunFieldsAt
    iframe Hltg Hstf Hcpo Hcpf Herb Herf Hgok Hlc Hlcn Hcancel0 Hstop Hdone Hstb Hci'
    iunfold context.cancelSpec
    iexact Hcancel
  -- the apply thread's resources
  iunfold applyBuiltC at Happ
  icases Happ with ⟨%st₀, %a, %t, %f, Hth, %Hlo, Hbe, Hca, Halg, Hbm, Hrdk, Hbo, ⟨%ua, Hua, Hres, #Hfor, Hkv⟩, HRA,
    Hrdat, Hao, #Hlog, Hkr, Hrest, Hap, Hfs, Htok⟩
  -- the read side, from the component's row (`acRes_read`)
  icases acRes_read C s E ua srvAuthSt0 hm $$ Hres with ⟨Hres, #HaR⟩
  -- (D22 J1b) the snapshot path's resources to the apply thread, its persistent bundle to `run`
  icases srvSnapOwn_of_boot s ci E γr γ ai₀ $$ Hsnapb with ⟨Hso, #Hsnapb⟩
  ihave Hstart : applyStartC C s γ ci b E γr ai₀ c₀ x₀ γw $$
      [Hth Hbe Hca Halg Hbm Hrdk Hbo Hua Hkv HRA Hres Hrdat Hao Hkr Hrest Hap Hfs Htok Hwg1 HRD Hso]
  · iunfold applyStartC
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Halg Hbm Hrdk Hao Hso Hfs Hwg1 Hlog Hkr Hrest Hap Htok
    isplitr
    · ipureintro; exact Hlo
    iunfold srvApplyKVC
    iexists ua
    isplitl [Hua]
    · iexact Hua
    isplitr
    · iexact Hfor
    isplitl [Hkv]
    · iexact Hkv
    isplitl [Hbo]
    · iexact Hbo
    isplitl [HRA]
    · iexact HRA
    isplitl [Hres]
    · iexact Hres
    isplitr [Hrdat]
    · iexists w, RD
      isplitr
      · iexact Hw
      isplitr
      · iapply isWait_waitOk $$ Hwait
      iexact HRD
    iexact Hrdat
  -- the views (before the compactor's run, whose precondition `NewServer` makes from them)
  icases Hreqb with ⟨%vq, #Hvq⟩
  iunfold srvReqBuiltM at Hvq
  icases Hvq with ⟨#Q1, #Q2, #Q3, #Q4, #Q5, #Q6, #Q7, #Q8, #Q9, #Q10, #Q11, #Q12, #Q13, #Q14,
    #Q15, #Q16, #Q17, #Q18, %Q19⟩
  ihave #Hreq : isServerReqM C.isOn s E { ρ with wait := γw } $$ []
  · iapply (isServerReqM_split C.isOn s E _).2
    isplitl; rotate_left
    · iapply srvAuthBoundM_of_read C s E hm $$ HaR
    iexists { vq with w := w, done := dch }
    iunfold srvReqFieldsAtM
    iframe Q18 Q16 Q15 Q14 Q13 Q12 Q11 Q10 Q9 Q8 Q7 Q6 Q5 Q4 Q3 Q2 Q1 Hdone Hw
    isplitr
    · iunfold waitInvM
      isplitr
      · iexists RD
        have hwr : reqWaitRM (GF := GF) C.isOn { ρ with wait := γw } E = reqWaitRM C.isOn ρ E := rfl
        rw [hwr]
        iexact Hwait
      iexact Hwn
    isplitr
    · iunfold srvDoneChan
      iexists γd, _
      iexact HdcU
    isplitr
    · iunfold srvIndexInvsM
      iexists γr
      iframe Hci' Hai
    have hmint : srvMintInv (GF := GF) { ρ with wait := γw } = srvMintInv ρ := rfl
    rw [hmint]
    iframe Q17
    -- (M2's apply side, item 19) the KV names' mode and the certificates' invariant, the apply
    -- side's (`srvKVInvs`)
    ihave #Hkvt := Hkvi
    iunfold srvKVInvsC at Hkvt
    icases Hkvt with ⟨-, #HkcI, -, -, -, -, %Hktie, -, -⟩
    have hkv : ({ ρ with wait := γw } : ReqNames).kv = γr.kv := by subst Hρrd; rfl
    have hrf : ({ ρ with wait := γw } : ReqNames).raft = γr.raft := by subst Hρrd; rfl
    rw [hkv, hrf]
    iframe HkcI
    ipureintro; exact ⟨kvTieM_of_names _ E γr Hktie, Q19⟩
  icases Hrdb with ⟨%vd, #Hvd⟩
  iunfold srvReadBuilt at Hvd
  icases Hvd with ⟨#R1, #R2, %R3, #R4, #R5, #R6, #R7, #R8, #R9, #R10, #R11, #R12, #R13⟩
  let awi : GoInterface :=
    interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.timeList.ty) #tl
  ihave #Hrd : isServerReadM C.isOn s E γr $$ []
  · iunfold isServerReadM
    iexists ({ vd with read := rd, aw := awi, lc := lcn, stopping := sgc } : ReadFields)
    iunfold srvReadFieldsAtM
    iframe R13 R12 R11 R10 R8 R7 R6 R5 R4 R2 R1 Hwt Hlc Hread Hisrd Hstopping Haw Hci' HkviM Hai
    isplitr
    · ipureintro; exact R3
    isplitr
    · iexact R9
    isplitl
    · iunfold stopChan
      iexists γsg
      iexact HsgU
    iapply readBound_of_read C s E vd.auth hm $$ [$HaR $R6]
  -- `go s.run()`, with the write budget backed by time receipts (D19b; made by `NewServer` since
  -- M2's item 15, stage B3)
  iunfold srvWTBudget at HWB
  icases HWB with ⟨%γp, #HWB, #HWA0, HWreg⟩
  -- (H2, 2026-11-05) the budget's register set to `GoAttach`'s receipts' name, for good
  imod dghostVar_update (some γg.run) γp.reg none $$ HWreg with HWreg
  imod dghostVar_persist γp.reg 1 _ $$ HWreg with #HWreg
  -- `if s.compactor != nil { s.compactor.Run() }` (the fork's fix: `start()` runs the compactor,
  -- `nonissues/etcd-compactor-started-before-start.md`): its run, once (`compactorRun`; M2, S4)
  icases Hcrun with ⟨%cr, #Hcra, Hcr⟩
  ihave %Hcreq := typedPointsto_agree_wand _ _ _ _ _ $$ Hcra Hcpf
  subst Hcreq
  wp_join iprop(s_ptr ↦ s) at next with [s Hcr] as s
  · iunfold compactorRun at Hcr
    icases Hcr with (%Hcpn | ⟨%Hoff, %T, %P, #Hcp, HT, HP⟩)
    · rw [Hcpn]
      (try wp_auto)
      wp_join_done
    -- the run's precondition, from the views (auth off, `compactorRun`'s)
    have hCoff : C.isOn = false := by
      rw [← AuthC.mode_isOn, ← hm, ← apply.AEnv.authOn_eq]; exact Hoff
    ihave #Hreq0 : isServerReq s E { ρ with wait := γw } $$ []
    · rw [← isServerReqM_false, ← hCoff]; iexact Hreq
    ihave #Hrd0 : isServerRead s E γr $$ []
    · rw [← isServerReadM_false, ← hCoff]; iexact Hrd
    ihave Hcred0 := HNR
    imod Hcred0 with #Hcred
    imod HP $$ %({ ρ with wait := γw } : ReqNames) [] with HP
    · iframe Hpkg Hreq0 Hcred
      subst Hρrd; iexact Hrd0
    icases v3compactor.compactorOk_Run _ _ _ $$ Hcp with ⟨%ci, %Hci, #HRun⟩
    rw [Hci]
    (try wp_auto)
    wp_apply HRun $$ [HT HP]
    · iframe HT HP
    (try wp_auto)
    wp_join_done
  -- (revoke-open, 2026-11-06) the outer pool's read-loop slots, and the revocation's bundle
  icases replicate_takeN _ srvRevokePoolN _ (by
      unfold srvRevokePoolN backend.rdPoolN; rw [sync.rwmutex.actualMaxReaders_unseal]; decide)
    $$ Hrslots with ⟨HrdB, Hrslots⟩
  ihave HBp : [∗list] _x ∈ List.replicate srvRevokePoolN (),
      iprop(srvWgReaderAt s γg ∗ srvReadReader s γr) $$ [HwgB HrdB]
  · -- (no bare `iframe` over these `2 ^ 28 - 1`-long lists: a mismatched `[∗list]` unfolds the
    -- `List.replicate`)
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [HwgB]
    · iexact HwgB
    · iapply replicate_map _ _ (srvReadAddr s ↦□ rd) $$ [$Hread $HrdB]
      iintro ⟨#Hr, Hslot⟩
      iunfold srvReadReader
      iexists rd
      iframe Hr Hslot
  imod threadPool.initL srvRevokeOuterN 2 iprop(srvWgReaderAt s γg ∗ srvReadReader s γr) ⊤
      srvRevokePoolN (by unfold srvRevokePoolN; omega) $$ HBp with ⟨%γB, #HBp⟩
  ihave #Hrvk : srvRevokeCtx s E { ρ with wait := γw } γr γg $$ []
  · iapply srvRevokeCtx_intro
    iframe Hrvkb
    isplitr
    · iapply srvRevokeOuterPool_intro s γr γg γB $$ HBp
    isplitr
    · iintro !> %Hoff
      have hCoff : C.isOn = false := by
        rw [← AuthC.mode_isOn, ← hm, ← apply.AEnv.authOn_eq]; exact Hoff
      isplitr
      · rw [← isServerReqM_false, ← hCoff]; iexact Hreq
      · rw [← isServerReadM_false, ← hCoff]; iexact Hrd
    iframe HNR
    iexists cctx, _
    iframe Hctx Hcctx Hcspan Hcst
  -- (R2d'a swap batch 5) `run`'s start conjuncts in restart form, from a first start's (`%HEr`,
  -- `Hsnap`, `Hstart`; `srvRunRestartR_first`)
  ihave HRr : srvRunRestartR C s γ ci b E { ρ with wait := γw } γr Er γn ai₀ at₀ c₀ x₀ γw
      $$ [Hsnap Hstart]
  · iapply (srvRunRestartR_first C s γ ci b E { ρ with wait := γw } γr Er γn ai₀ at₀ c₀ x₀ γw HEr)
    isplitl [Hsnap]
    · iexact Hsnap
    · iexact Hstart
  -- (revoke-open Q8 (a)) `run` forked with the fresh thread token
  wp_apply wp_fork_tok_body $$ [HRr Hloop Hsend Happly Hrdone Hcomm Hdc Hclose Hlr Hwpend Hrunh
      Hwth Hwtl Hskeep]
  · iintro Htok
    wp_apply hRun s γ ci TM C E { ρ with wait := γw } γr Er γn γg γcx γd
      ⟨vr.errorc, stc, dch, cancel, vr.compactor, vr.stats, lcn⟩ b ai₀ at₀ c₀ x₀ cfgk.DataDir' cs
      $$ [HRr Hloop Hsend Happly Hrdone Hcomm Hdc Hclose Hlr Hwpend Hrunh Hwth Hwtl Hskeep Htok]
      as Htok
    · simp only [srvStopReq_wait, srvDoneInv_wait]
      iframe Htok
      iunfold isServerRunC
      iframe
      iframe Hrf Hrvk Hsa Hsrv Hrn Hlnil Hmid HmetaSnap
      isplitr
      · ipureintro; exact ⟨hm, hRB⟩
      isplitr
      · ipureintro; exact Hdisk
      isplitr
      · ipureintro; exact Hslg
      isplitr
      · iexists vd.kv; iframe R1 R2; ipureintro; exact R3
      iframe Hsnapb
      isplitr
      · iexists γp
        iframe HWB HWreg
        rw [Hai0]; iexact HWA0
      iexists _, _; iframe Hsc Hscu
    iframe Htok
    ipureintro; exact isPanic_intoVal ()
  -- what `Start`'s goroutines and the request path get
  ihave #Hrs := isReadServer_of_serverM C.isOn hAW hDone hStop hLC hFC hNRID hRT (hAI C.isOn) hLg s E
    { ρ with wait := γw } γr Hρrd $$ [$Hpkg $Hreq $Hrd]
  -- the minted contexts (2026-10-16, stage R7b): from the mint and raft's commit invariant
  ihave #Hmint : readCtxMinted (GF := GF) γr $$ []
  · ihave #Hkvi3 := Hkvi
    iunfold srvKVInvsC at Hkvi3
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
  · rw [← HEr.2.1]
    iapply isReadRaft_of_raftNode hRSt hRI Er γn (srvRAddr s) $$ [$Hpkg $Hrn]
  icases replicate_take1 _ _ (by have := sync.actualMaxReaders_ge_2; omega) $$ Hlcslots with ⟨Hlc1, Hlcslots⟩
  ihave HWBx : iprop(∃ (γp : WTNames) (γg : GoNames), srvWTPool (GF := GF) E γp ∗
      dghostVar γp.reg DFrac.discard (some γg.run) ∗ srvWgReaderAt s γg ∗
      ∃ dd : GoString, srvStopRight (GF := GF) s E ρ.rd.raft.raft ρ γn.id dd) $$ [Hwg2 Hright]
  · iexists γp, γg; iframe HWB HWreg Hwg2 Hright
  iapply HΦ
  iexists γw
  ihave #HauLb := acRead_lb C s E $$ HaR
  iframe Hreq Hrd HauLb HWBx
  iunfold srvStarted
  iframe Hwgs HNR
  isplitr
  · ipureintro; exact Hρrd
  isplitr
  · iexists rd
    iframe Hread
    iapply Hrlp $$ Hrs Hrr [] Hmint
    iapply readCompose_C C s E γr $$ Hkvi
  isplitl [Hlrl Hlc1 Hfcr]
  · iunfold srvReadLR
    isplitl [Hlrl]
    · iexact Hlrl
    iframe Hfcr
    iexists lcn
    iframe Hlc Hlc1
  isplitl [Hrslots]
  · -- (the count's name, `srvStartReadN`, unfolded in this conjunct's goal only)
    unfold srvStartReadN
    iapply replicate_map _ _ (srvReadAddr s ↦□ rd) $$ [$Hread $Hrslots]
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
