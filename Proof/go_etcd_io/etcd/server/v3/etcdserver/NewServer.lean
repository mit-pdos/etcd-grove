/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean`. Lean-first (no Rocq
counterpart); placed at the server-construction unit's stage N0 (2026-10-16), unit N1's to prove
(D13 and D13a-d, `notes/decisions.md`). The hypotheses are the callees' specs in the order of
`etc/link-lean-first-server.txt` (`NewServer: …`); raft's node methods are for the raft wrapper's
composition (`raftNode_of_StartNode`, `NodeStart.lean`, restated with the environment chosen
before the call: N1).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__With
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlice
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.NewGenerator
public import Spec.go_etcd_io.etcd.pkg.v3.notify.NewNotifier
public import Spec.go_etcd_io.etcd.server.v3.auth.NewAuthStore
public import Spec.go_etcd_io.etcd.server.v3.auth.NewTokenProvider
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__PeerDialTimeout
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FeatureEnabled
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__NewUberApplier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__restoreAlarms
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.addFeatureGateMetrics
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetVersionChangedNotifier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__String
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddRemote
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewLeaderStats
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewServerStats
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newCorruptionChecker
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__HashStorage
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewAuthBackend
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__ReadIndex
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.math.Ceil
public import Spec.time.Duration__Seconds_ptr
public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__OnPreCommitUnsafe
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__UnsafeSave
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafePut
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__ID
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__IsSafeRangeBucket
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__GetLease
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Attach
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Detach
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__SetRangeDeleter
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Grant
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Checkpoint
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__TTL
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Promote
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Demote
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__ExpiredLeasesC
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ConcurrentReadTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ReadTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ForceCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Size
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SizeInUse
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockInsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockOutsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeSeqPut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeCreateBucket
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorContract
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildAlloc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Perennial.Proof.time
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.FloatToInt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- A blank struct field's conjunct (`"_" ∷ True`, which `iNamed` leaves anonymous) renamed to be
cleared (`"-"`): `wp_for` names every hypothesis of the context. -/
theorem named_blank_clear {A : Type _} (P : A) : Perennial.named "_" P = Perennial.named "-" P := rfl

set_option maxRecDepth 100000 in
set_option pp.maxSteps 200000 in
set_option maxHeartbeats 0 in
theorem NewServer.wp_proof
    (h0 : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h1 : zap.Error.spec (GF := GF) (hG := hG))
    (h2 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h3 : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h4 : v2stats.NewServerStats.spec (GF := GF) (hG := hG))
    (h5 : membership.RaftCluster.String.spec (GF := GF) (hG := hG))
    (h6 : v2stats.NewLeaderStats.spec (GF := GF) (hG := hG))
    (h7 : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (h8 : bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG))
    (h9 : node.Ready.spec (GF := GF) (hG := hG))
    (h10 : node.Advance.spec (GF := GF) (hG := hG))
    (h11 : node.Tick.spec (GF := GF) (hG := hG))
    (h12 : node.ReadIndex.spec (GF := GF) (hG := hG))
    (h13 : types.URLs.StringSlice.spec (GF := GF) (hG := hG))
    (h14 : idutil.NewGenerator.spec (GF := GF) (hG := hG))
    (h15 : notify.NewNotifier.spec (GF := GF) (hG := hG))
    (h16 : addFeatureGateMetrics.spec (GF := GF) (hG := hG))
    (h17 : prometheus.GaugeVec.With.spec (GF := GF) (hG := hG))
    (h18 : membership.RaftCluster.SetVersionChangedNotifier.spec (GF := GF) (hG := hG))
    (h19 : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (h20 : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG))
    (h21 : EtcdServer.FeatureEnabled.spec (GF := GF) (hG := hG))
    (h22 : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (h23 : math.Ceil.spec (GF := GF) (hG := hG))
    (h24 : lease.NewLessor.spec (GF := GF) (hG := hG))
    (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
    (h26 : mvcc.New.spec (GF := GF) (hG := hG))
    (h27 : newCorruptionChecker.spec (GF := GF) (hG := hG))
    (h28 : mvcc.store.HashStorage.spec (GF := GF) (hG := hG))
    (h29 : schema.NewAuthBackend.spec (GF := GF) (hG := hG))
    (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG))
    (h31 : v3compactor.New.spec (GF := GF) (hG := hG))
    (h32 : EtcdServer.restoreAlarms.spec (GF := GF) (hG := hG))
    (h33 : EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG))
    (h34 : EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (h35 : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (h36 : config.ServerConfig.PeerDialTimeout.spec (GF := GF) (hG := hG))
    (h37 : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (h38 : rafthttp.Transport.Start.spec (GF := GF) (hG := hG))
    (h39 : rafthttp.Transport.AddRemote.spec (GF := GF) (hG := hG))
    (h40 : membership.RaftCluster.Members.spec (GF := GF) (hG := hG))
    (h41 : rafthttp.Transport.AddPeer.spec (GF := GF) (hG := hG))
    (h42 : mvcc.watchableStore.Close.spec (GF := GF) (hG := hG))
    (h43 : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (h44 : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (h45 : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (h46 : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (h47 : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (h48 : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (h49 : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (h50 : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (h51 : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (h52 : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (h53 : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (h54 : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (h55 : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (h56 : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (h57 : lease.lessor.Promote.spec (GF := GF) (hG := hG))
    (h58 : lease.lessor.Demote.spec (GF := GF) (hG := hG))
    (h59 : lease.lessor.ExpiredLeasesC.spec (GF := GF) (hG := hG))
    (h60 : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (h61 : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (h62 : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (h63 : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (h64 : backend.backend.Size.spec (GF := GF) (hG := hG))
    (h65 : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (h66 : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (h67 : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (h68 : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (h69 : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (h70 : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (h71 : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (h72 : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (h73 : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (h74 : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (h75 : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (h76 : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (h77 : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG)) :
    NewServer.spec (GF := GF) (hG := hG) := by
  intro cfg γ bud id bootLog ρ E₀ N HρRaft Hpol Hc0 Hch0 Hlog0 Hcok Hlgnn Hcbl Hacr Hfgp
  wp_start
  iNamed Hpre
  wp_apply wp_with_defer as %defer defer
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hboot' := Hboot
  iunfold bootstrapContract at Hboot'
  wp_apply Hboot' as %b %err Hb
  icases Hb with (%Herr | ⟨%Herr, Hb⟩)
  · -- `bootstrap` failed
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    wp_apply h1 as %f -
    wp_apply wp_slice_literal (l := [f])
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply h0
    · ipureintro; exact Hlgnn
    iapply HΦ
    ileft
    ipureintro; exact ⟨rfl, Herr⟩
  subst Herr
  iNamed Hb
  iStructNamed Hbc
  wp_auto
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hspkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats $$ []
  · iPkgInit
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  wp_apply h2
  · ipureintro; exact Hlgnn
  wp_apply h5 as %cls -
  · iexact Hrc
  wp_apply h4 as %sstats %Hssnn
  (try wp_auto)
  wp_apply h7 $$ [$nodeID] as %ids nodeID
  wp_apply h6 as %lstats %Hlsnn
  (try wp_auto)
  -- the server's literal: `readych`, `lgMu`, `errorc`, the raft wrapper
  wp_apply chan.wp_make1 (V := Unit) as %rdc %γrdc ⟨#Hrdc, %Hrdcap, Hrdo⟩
  (try wp_auto)
  wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %errc %γec ⟨#Herrc, %Herrcap, Herro⟩
  · ipureintro; word
  imod start_bag (V := GoInterface) (fun _ => iprop(True)) _ errc γec (by trivial) $$ Herrc Herro
    with #Herrb
  (try wp_auto)
  -- `b.raft.newRaftNode(b.ss, b.storage.wal.w, b.cluster.cl)`: raft's node started
  -- (`NodeStartSpec`, `raftNode_of_StartNode`)
  have hNS := raftNode_of_StartNode (GF := GF) (MemStorReg.memStorRegName GF) h8 h9 h10 h11 h12
  obtain ⟨Hrlg, Hrhb, Hrvalid, Hrlok, Hrstor, Hrinfl, Hrcq, Hrdpf, Hrro, Hrdccv, Hrsizes, Hrasync,
    Hrpv, Hrapplied, Hrid, Hrps, Hrpsne, Hrnodup, Hr0, Hrpslen, Hrmem, Hrcfg, Hrboot, Hrbok⟩ := Hraft
  wp_apply (hNS (srvEr ρ E₀ (W64 0) (W64 0) bootKV bud) γ bud bs.raft' bs.ss' bw.w' bc.cl'
    (DFrac.own 1) bv cv lok γs pv ps ctxs bootLog Hrlg Hrhb Hrvalid Hrlok Hrstor Hrinfl Hrcq Hrdpf
    Hrro Hrdccv Hrsizes Hrasync Hrpv Hrapplied Hrps Hrpsne Hrnodup Hr0 Hrpslen Hrmem Hrcfg Hrboot
    Hrbok (by simp [srvEr, HρRaft]) (by simp [srvEr, HρRaft]) (by simp [srvEr, HρRaft])
    (by simpa [srvEr] using Hpol)) $$ [Hbv Hc Hstor Hpeers Hghost]
    as %r ⟨%γw, %rv, %Hrnames, Hr, Hrtm, Hloop, Happly, #Hrli, Hinst, Hbv, Hpeers⟩
  · iframe Hbv Hc Hstor Hpeers
    rw [Hrid]
    iframe Hghost
    iframe #
    iintro %γw' %hw
    iapply Hfits
    ipureintro; exact ⟨hw.1, hw.2.1, hw.2.2.2.1⟩
  (try wp_auto)
  -- the configuration, field by field from here on
  iStructNamed cfg
  ihave %HcuNN := typedPointsto_not_null _ _ _ $$ ClientURLs
  wp_apply h13 as %cus -
  · iframe #; ipureintro; exact HcuNN
  (try wp_auto)
  -- the request ids' generator, the notifiers
  ihave #Hipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil $$ []
  · iPkgInit
  ihave #Hnpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  wp_apply time.wp_Now as %now -
  wp_apply (h14 ρ.ids _ now (srvFloorFact E₀)) $$ [Hids] as %gen ⟨#Hgen, Hidcred⟩
  · iframe #; iframe Hids
  (try wp_auto)
  wp_apply h15 as %fcn ⟨#Hfcn, Hfcnr⟩
  wp_apply h15 as %cvn ⟨#Hcvn, Hcvnr⟩
  (try wp_auto)
  -- the server `s`, field by field
  generalize hsrv : «$r0_ptr» = s
  irename «$r0» => Hs
  iStructNamed Hs
  -- the metrics
  ihave Hsi : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold srvInit at Hsi
  icases Hsi with ⟨⟨-, -, -, -, -, ⟨%gvf, #Hgvf⟩, ⟨%gvi, #Hgvi⟩⟩, -⟩
  (try wp_auto)
  wp_apply h16 $$ []
  · iframe #; ipureintro; exact Hfgp
  ihave #Hppkg : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply h7 $$ [$nodeID] as %ids2 nodeID
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %lbl Hlbl
  wp_apply wp_mapInsert go.string lbl _ _ _ $$ [$Hlbl] as Hlbl
  (try wp_auto)
  wp_apply h17 as %gsi ⟨%gi, %Hgi, #Hgset⟩
  subst Hgi
  (try wp_auto)
  wp_apply Hgset
  (try wp_auto)
  wp_apply h18 $$ []
  · iframe #
  (try wp_auto)
  -- `lgMu`'s readers (`Logger()`)
  ipersist lg
  ipersist lgMu
  imod sync.init_RWMutex (fun _ => iprop(True)) (E := ⊤) «$v2_ptr» $$ [] «$v2» with Hlgrs
  · inext; itrivial
  ihave Hlgrs := replicate_map _ (srvLgReader s) (srvLgMuAddr s ↦□ «$v2_ptr») _
    (by iintro ⟨#H, Hm⟩; iunfold srvLgReader; iexists _; iframe Hm; iexact H) $$ [$lgMu $Hlgrs]
  -- `srv.Cfg`, field by field
  iStructNamedSuffix Cfg "S"
  ipersist ElectionTicksS
  ipersist TickMsS
  ipersist ServerFeatureGateS
  ipersist be
  have hMR : 100 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  have hM1 : 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by omega
  icases replicate_take1 _ _ hM1 $$ Hlgrs with ⟨Hlr1, Hlgrs⟩
  wp_apply h19 $$ [Hlr1] as ⟨-, Hlr1⟩
  · iframe #; iframe Hlr1; ipureintro; exact Hlgnn
  (try wp_auto)
  ihave #Htmpkg : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hmapkg : isPkgInit (PROP := IProp GF) pkg_id.math $$ []
  · iPkgInit
  wp_apply h22 $$ [$minTTL] as %secs minTTL
  wp_apply h23 as %ceil -
  (try wp_auto)
  ihave #Hfg' := Hfg
  iunfold isFeatureGate at Hfg'
  icases Hfg' with ⟨%fgi, %Hfgi, #Hen⟩
  rw [Hfgi]
  (try wp_auto)
  wp_apply Hen as %ckpp -
  (try wp_auto)
  wp_apply h20 $$ [] as %reqto -
  · iframe #
  (try wp_auto)
  -- the backend, over the server's hooks (`backend_server_hooks_of`)
  obtain ⟨Hbe0, HbP, Hci0, HhP⟩ := Hbe
  ihave #Hstpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hbkpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hscpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Hlspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  ihave #HB := backend_server_hooks_of h43 h44 h45 h76 h46 h47 h48 γA cil d.γB d.P (mvcc.lateW d.gx)
    d.be bh lgh Hci0 HhP $$ [$Hstpkg $Hbkpkg $Hscpkg $Hcipkg $Hhooks $HbeNH $HisCI $Hcons]
  icases Hopen with ⟨%qo, Hopen⟩
  rw [show N + 7 = (N + 6) + 1 by omega]
  icases ownToks_add_1 1 (N + 6) d.γB.wb $$ Hwb with ⟨Hwb, Hwl⟩
  -- `lease.NewLessor`
  rw [Hbe0]
  wp_apply (h24 cfg.Logger' _ _ d (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) qo)
    $$ [Hopen Hwl Hfl]
    as %l ⟨Hopen, %lp, %γl, %Hl, #Hlinv, #Hlcfg, #Hlexp, Hlrd, Hlown, #Hlck, #Hlbe, #Hllk⟩
  · iframe #
    unfold backend.wbTok
    iframe Hopen Hwl Hfl
    ipureintro; exact ⟨Hlgnn, Hckok⟩
  (try wp_auto)
  -- `auth.NewTokenProvider`
  ihave #Hapkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  wp_func_lits
  wp_apply h25 as %tp %terr %Htp
  · ipureintro; exact Hlgnn
  (try wp_auto)
  cases terr with
  | ok ei =>
    -- the token provider failed: the error returned, `b` closed by the deferred function
    wp_auto
    wp_apply h1 as %f -
    wp_apply wp_slice_literal (l := [f])
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply h3
    · ipureintro; exact Hlgnn
    wp_apply Hclose
    iapply HΦ
    ileft
    ipureintro; exact ⟨rfl, by simp⟩
  | nil => ?_
  have Htpnn := Htp rfl
  (try wp_auto)
  -- `mvcc.New`: the watchable store over the real backend (`server_kv_watchable_of`)
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨Hlr2, Hlgrs⟩
  wp_apply h19 $$ [Hlr2] as ⟨-, Hlr2⟩
  · iframe #; iframe Hlr2; ipureintro; exact Hlgnn
  (try wp_auto)
  subst Hl
  ihave #Hmvpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hisl := lease.isLessor_of_lessorInv h49 h50 h51 h52 lp γl $$ [$Hlspkg $Hlinv]
  rw [show N + 6 = 4 + (N + 2) by omega]
  icases (ownToks_add (N + 2) 4 d.γB.wb).1 $$ Hwb with ⟨Hwb, Hwkv⟩
  wp_apply (server_kv_watchable_of h26 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73
      h74 h75 h76 h77 h46 h47 h48 cfg.Logger' (lease.lessorIface lp) _ d HbP E₀.γ.bucket γl
      (batchLockInv γA (metaTM d.γB d.P)) #func.nil N E₀.γ.idx E₀.γ.cok Hcbl)
    $$ [Hview Hlate Hwkv Hrts Hlrd Hidx Hcok]
    as %ws ⟨%st, %γw, %Hγw, #HisKV, ⟨%rv, #Hrvf, #Hrv⟩, #HhkI, Hkvw, Hwts, Hcok, #Hws, Hwtoks,
      Hwrds, Hwcl⟩
  · iframe #
    iframe Hview Hlate Hwkv Hrts Hlrd Hidx Hcok
  (try wp_auto)
  ihave #Hws' := Hws
  iunfold mvcc.isWatchableStore at Hws'
  icases Hws' with ⟨%wvc, %wstc, %wrv, %wγv, Hws'⟩
  iNamed Hws'
  -- `newCorruptionChecker(lg, srv, srv.kv.HashStorage())`
  rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty)
    (m := go!"HashStorage")]
  wp_call
  (try wp_auto)
  wp_apply h28 $$ [] as %hst -
  · iframe #
  wp_apply h27 as %cc -
  (try wp_auto)
  -- `auth.NewAuthStore(srv.Logger(), schema.NewAuthBackend(srv.Logger(), srv.be), tp, …)`
  icases replicate_take2 _ _ (by omega) $$ Hlgrs with ⟨Hlr3, Hlr4, Hlgrs⟩
  wp_apply h19 $$ [Hlr3] as ⟨-, Hlr3⟩
  · iframe #; iframe Hlr3; ipureintro; exact Hlgnn
  wp_apply h19 $$ [Hlr4] as ⟨-, Hlr4⟩
  · iframe #; iframe Hlr4; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply h29 as %ab ⟨%abl, %Hab, #Hablg, #Habbe⟩
  (try wp_auto)
  rw [show (4 : Nat) = 2 + 2 from rfl]
  icases (ownToks_add 2 2 d.γB.wb).1 $$ Hwb with ⟨Hwb, Hwa⟩
  wp_apply (h30 cfg.Logger' ab tp _ abl d (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) qo)
    $$ [Hopen Hhook Hwa Hfa]
    as %ast ⟨Hopen, Hhook, %RD, HRD, #HisReq, #HisAuth⟩
  · iframe #
    iframe Hopen Hhook Hwa Hfa
    ipureintro; exact ⟨Hlgnn, Htpnn, Haufit, Hab⟩
  (try wp_auto)
  -- the compactor is off (`AutoCompactionRetention = 0`)
  rw [Hacr]
  (try wp_auto)
  -- `srv.restoreAlarms()`
  ihave #Hbef : srvBeAddr s ↦□ (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be : GoInterface) $$ []
  · rw [← Hbe0]; iexact be
  rw [show (2 : Nat) = 1 + 1 from rfl]
  icases (ownToks_add 1 1 d.γB.wb).1 $$ Hwb with ⟨Hwb, Hwal⟩
  wp_apply (h32 s cfg.Logger' d (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) qo _)
    $$ [Hopen Hwal alarmStore] as %aerr ⟨Hopen, Hares⟩
  · iframe #
    unfold backend.wbTok
    iframe Hopen Hwal alarmStore
    ipureintro; exact Hlgnn
  icases Hares with (⟨%Haerr, -⟩ | ⟨%Haerr, %alst, %Halnn, alarmStore, #HalS, #HalA⟩)
  · -- the alarms could not be restored: the error returned, the store and `b` closed
    cases aerr with
    | nil => exact absurd rfl Haerr
    | ok ei => ?_
    wp_auto
    wp_apply h42 $$ [Hwcl]
    · iframe #; iframe Hwcl
    (try wp_auto)
    wp_apply Hclose
    iapply HΦ
    ileft
    ipureintro; exact ⟨rfl, by simp⟩
  subst Haerr
  (try wp_auto)
  -- `srv.uberApply = srv.NewUberApplier()`: its contract given once the hook is installed
  ipersist kv
  ipersist alarmStore
  ipersist authStore
  ipersist lessor
  ipersist cluster
  ipersist consistIndex
  ipersist QuotaBackendBytesS
  ipersist WarningApplyDurationS
  wp_apply (h33 s cfg.Logger' alst bc.cl' _ _ _ _ _ _ cfg.QuotaBackendBytes'
      cfg.WarningApplyDuration' RD) $$ [HRD]
    as %ua ⟨%up, %uopts, %Hua, %Huopts, Hulate⟩
  · iframe #; iframe HRD
  (try wp_auto)
  -- the checkpointer, if the feature is on (`lessorCkptOk`; its later calls: `ckptEffectsOk`)
  ihave #Hlck' := Hlck
  iunfold lessorCkptOk at Hlck'
  icases Hlck' with ⟨%lci, %Hlci, #Hsetcp⟩
  wp_apply h21 as %fe -
  · iframe #
  unfold lease.lessorIface at Hlci
  cases Hlci
  wp_join iprop(srv_ptr ↦ s) with [srv] as srv
  · wp_func_lits
    wp_apply Hsetcp
    (try wp_auto)
    wp_join_done
  (try wp_auto)
  -- the post-lock hook: `srv.be.SetTxPostLockInsideApplyHook(srv.getTxPostLockInsideApplyHook())`
  ihave #HsCI : isServerCI s γA cil $$ []
  · iunfold isServerCI
    rw [← Hci.1]
    iframe #
  wp_apply (h34 s γA cil (metaTM d.γB d.P)) as %hook ⟨%Hhknn, #Hhks⟩
  · iframe #
  (try wp_auto)
  wp_apply (h35 d.γB d.P (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) d.be qo func.nil hook)
    $$ [Hopen Hhook Hwb] as ⟨Hopen, Hhook⟩
  · iframe #
    unfold backend.wbTok
    iframe Hopen Hhook Hwb
  imod (backend.plHook_persist (GF := GF) d.γB hook) $$ Hhook with #Hhook
  (try wp_auto)
  -- the transport
  ihave #Hcfgpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Hmbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hrhpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
  · iPkgInit
  ipersist ElectionTicks
  ipersist TickMs
  wp_apply h36 as %pdt -
  · iframe #
  (try wp_auto)
  wp_apply h37 as -
  · iframe #
  (try wp_auto)
  generalize htr : «$r0_ptr» = t
  wp_apply (h38 t) $$ [«$r0»] as %terr Htres
  · iframe #; iframe «$r0»
    ipureintro; exact ⟨Htrok, Hlgnn, Hssnn, Hlsnn⟩
  icases Htres with (%Hterr | ⟨%Hterr, Htlive, Htstart⟩)
  · -- the transport could not start: the error returned, the store and `b` closed
    cases terr with
    | nil => exact absurd rfl Hterr
    | ok ei => ?_
    wp_auto
    wp_apply h42 $$ [Hwcl]
    · iframe #; iframe Hwcl
    (try wp_auto)
    wp_apply Hclose
    iapply HΦ
    ileft
    ipureintro; exact ⟨rfl, by simp⟩
  subst Hterr
  (try wp_auto)
  -- `for _, m := range b.cluster.remotes { if m.ID != b.cluster.nodeID { tr.AddRemote(…) } }`
  ihave %Hrmsl := ownSlice_len _ _ _ $$ Hrms
  ihave IH : iprop(∃ (n : w64) (mm : Loc), "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mm ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z bc.remotes'.len⌝) $$ [i m]
  · iexists W64 0, _
    iframe i m
    ipureintro
    constructor
    · decide
    · have := Hrmsl.2; word
  -- the blank fields' leftovers (`"_" ∷ True`, anonymous) cleared, so `wp_for` can name the context
  rw [named_blank_clear (iprop(True) : IProp GF)]
  iNamed
  wp_for IH
  wp_if_destruct
  · obtain ⟨mx, Hmx⟩ : ∃ mx, rms[(sint.Z n).toNat]? = some mx :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hrmsl; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z bc.remotes'.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ _ mx Hn.1 $$ [] as -
    · iframe #; ipureintro; exact Hmx
    ihave #Hmro := (BigSepL.bigSepL_lookup (Φ := fun _ m => memberRO (GF := GF) m) Hmx) $$ Hrmsi
    iunfold memberRO at Hmro
    icases Hmro with ⟨%Hmnn, %mv, %mus, #Hmv, #Hmus, %Hmok⟩
    iStructNamedPrefix Hmv "M"
    iStructNamedPrefix MRaftAttributes "MR"
    (try wp_auto)
    wp_if_destruct
    · wp_for_post
      iframe
      iexists n + W64 1, _
      iframe
      ipureintro; constructor <;> word
    · wp_apply (h39 t mv.ID' mv.RaftAttributes'.PeerURLs' DFrac.discard mus) $$ [Htlive]
        as ⟨Htlive, -⟩
      · iframe #; iframe Htlive; ipureintro; exact ⟨Htrok, Hmok⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, _
      iframe
      ipureintro; constructor <;> word
  -- `for _, m := range b.cluster.cl.Members() { … tr.AddPeer(…) }`
  wp_apply h40 $$ [] as %msl ⟨%ms, Hmsat⟩
  · iframe #
  iunfold membership.membersAt at Hmsat
  icases Hmsat with ⟨Hmsl, Hmso⟩
  ihave %Hmsll := ownSlice_len _ _ _ $$ Hmsl
  ihave IH2 : iprop(∃ (n : w64) (mm : Loc), "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mm ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z msl.len⌝) $$ [i m]
  · iexists W64 0, _
    iframe i m
    ipureintro
    constructor
    · decide
    · have := Hmsll.2; word
  wp_for IH2
  wp_if_destruct
  · obtain ⟨mx, Hmx⟩ : ∃ mx, ms[(sint.Z n).toNat]? = some mx :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hmsll; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ _ mx Hn.1 $$ [Hmsl] as Hmsl
    · iframe Hmsl; ipureintro; exact Hmx
    icases (BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ m => membership.ownMember (GF := GF) m) Hmx)
      $$ Hmso with ⟨Hmo, Hmso⟩
    iunfold membership.ownMember at Hmo
    iunfold membership.memberIs at Hmo
    icases Hmo with ⟨%mid, %Hmnn, %mpu, %mcu, %mil, %mnm, %mpus, %mcus, Hmid, Hmpu, Hmil, Hmnm, Hmcu, Hmpus, Hmcus, %Hmok⟩
    (try wp_auto)
    wp_if_destruct
    · ihave Hmso : iprop([∗list] m ∈ ms, membership.ownMember (GF := GF) m)
          $$ [Hmso Hmid Hmpu Hmil Hmnm Hmcu Hmpus Hmcus]
      · ihave Hmso := Hmso $$ %(fun (_ : Nat) (m : Loc) => membership.ownMember (GF := GF) m)
        iapply Hmso
        · iintro !> %k %y %_ %_ H; iexact H
        · iunfold membership.ownMember; iexists _
          iunfold membership.memberIs
          isplitl []
          · ipureintro; exact Hmnn
          iexists mpu, mcu, mil, mnm, mpus, mcus
          iframe; ipureintro; exact Hmok
      wp_for_post
      iframe
      iexists n + W64 1, _
      iframe
      ipureintro; constructor <;> word
    · wp_apply (h41 t mid mpu (DFrac.own 1) mpus) $$ [Htlive Hmpus] as ⟨Htlive, Hmpus⟩
      · iframe #; iframe Htlive Hmpus; ipureintro; exact ⟨Htrok, Hmok⟩
      (try wp_auto)
      ihave Hmso : iprop([∗list] m ∈ ms, membership.ownMember (GF := GF) m)
          $$ [Hmso Hmid Hmpu Hmil Hmnm Hmcu Hmpus Hmcus]
      · ihave Hmso := Hmso $$ %(fun (_ : Nat) (m : Loc) => membership.ownMember (GF := GF) m)
        iapply Hmso
        · iintro !> %k %y %_ %_ H; iexact H
        · iunfold membership.ownMember; iexists _
          iunfold membership.memberIs
          isplitl []
          · ipureintro; exact Hmnn
          iexists mpu, mcu, mil, mnm, mpus, mcus
          iframe; ipureintro; exact Hmok
      wp_for_post
      iframe
      iexists n + W64 1, _
      iframe
      ipureintro; constructor <;> word
  -- `srv.r.transport = tr`; the result
  sorry

end proof

end EtcdGrove
end Perennial
