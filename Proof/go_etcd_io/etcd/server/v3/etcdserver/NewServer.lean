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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Term
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ForceSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ClusterVersion

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

/-- `leadTimeMu`'s resource is fractional (for `sync.init_RWMutex`). -/
instance leadTimeP_fractional (s : Loc) : Fractional (leadTimeP (GF := GF) s) := by
  unfold leadTimeP
  exact fractional_exists_agree
    (fun (t : time.Time) q => iprop(structFieldRef EtcdServer go!"leadElectedTime" s ↦{DFrac.own q} t))
    (fun t => fractional_of_dfractional
      (fun dq => typedPointsto (structFieldRef EtcdServer go!"leadElectedTime" s) t dq))
    (fun x y q1 q2 => by
      iintro ⟨H1, H2⟩
      icombine H1 H2 gives %H
      ipureintro; exact H)

/-- `bemu`'s resource is fractional (for `sync.init_RWMutex`). -/
instance bemuP_fractional (s : Loc) : Fractional (bemuP (GF := GF) s) := by
  unfold bemuP
  exact fractional_exists_agree
    (fun (b : GoInterface) q => iprop(srvBeAddr s ↦{DFrac.own q} b))
    (fun b => fractional_of_dfractional (fun dq => typedPointsto (srvBeAddr s) b dq))
    (fun x y q1 q2 => by
      iintro ⟨H1, H2⟩
      icombine H1 H2 gives %H
      ipureintro; exact H)

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
    (h77 : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (h78 : node.Propose.spec (GF := GF) (hG := hG))
    (h79 : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (h80 : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (h81 : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (h82 : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (h83 : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (h84 : EtcdServer.ClusterVersion.spec (GF := GF) (hG := hG)) :
    NewServer.spec (GF := GF) (hG := hG) := by
  intro cfg γ bud id bootLog ρ E₀ N HρRaft Hpol Hc0 Hch0 Hlog0 Hcok Hlgnn Hcbl Hacr Hbnd Hrb HrbN Hmid Hfgp
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
  have hNS := raftNode_of_StartNode (GF := GF) (MemStorReg.memStorRegName GF) h8 h9 h10 h11 h12 h78
  obtain ⟨Hrlg, Hrhb, Hrvalid, Hrlok, Hrstor, Hrinfl, Hrdpf, Hrro, Hrdccv, Hrsizes, Hrasync,
    Hrapplied, Hrid, Hrps, Hrpsne, Hrnodup, Hr0, Hrpslen, Hrmem, Hrcfg, Hrboot, Hrbok⟩ := Hraft
  wp_apply (hNS (srvEr ρ E₀ (W64 0) (W64 0) bootKV bud) γ bud bs.raft' bs.ss' bw.w' bc.cl'
    (DFrac.own 1) bv cv lok γs pv ps ctxs bootLog Hrlg Hrhb Hrvalid Hrlok Hrstor Hrinfl Hrdpf
    Hrro Hrdccv Hrsizes Hrasync Hrapplied Hrps Hrpsne Hrnodup Hr0 Hrpslen Hrmem Hrcfg Hrboot
    Hrbok (by simp [srvEr, HρRaft]) (by simp [srvEr, HρRaft]) (by simp [srvEr, HρRaft])
    (by simpa [srvEr] using Hpol)) $$ [Hbv Hc Hstor Hpeers Hghost]
    as %r ⟨%γrn, %rvr, %Hrnames, Hr, Hrtm, Hloop, Happly, #Hrli, Hinst, Hbv, Hpeers⟩
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
  wp_apply (h14 ρ.ids _ now (srvFloorFact E₀)) $$ [Hids] as %gen ⟨#Hgen, HNZ⟩
  · iframe #; iframe Hids
  -- the reserved id `0` (D19c): the member id's 16 low bits are not `0`
  ihave #HNZ0 := HNZ $$ %(by
    intro h
    apply Hmid
    rw [← Hid]
    have := congrArg (fun w : w16 => uint.Z w) h
    word)
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
  ihave ⟨Cfg, %HCfgnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Cfg
  iStructNamedSuffix Cfg "S"
  ipersist ElectionTicksS
  ipersist TickMsS
  ipersist ServerFeatureGateS
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
  -- the backend, from `backend.New`'s postcondition (`bootBackend_of_newPost`)
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
  ihave ⟨#HB, Hhook, Hopen, Hview, Hwb, Hrts⟩ := bootBackend_of_newPost d.γB d.P
    (fun _ => mvcc.lateW d.gx) (fun γB => batchLockInv γA (metaTM γB d.P)) d.be D N HD HN $$ Hnew
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
  -- the lessor's reader slots: one for the store, one for the apply thread's lease owner (D14i)
  icases replicate_take1 _ _ hM1 $$ Hlrd with ⟨Hlrd, Hlrds⟩
  icases replicate_take1 _ _ (by omega) $$ Hlrds with ⟨Hlrd2, -⟩
  wp_apply (server_kv_watchable_of h26 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73
      h74 h75 h76 h77 h46 h47 h48 cfg.Logger' (lease.lessorIface lp) _ d HbP E₀.γ.bucket γl
      (batchLockInv γA (metaTM d.γB d.P)) #func.nil N E₀.γ.idx E₀.γ.cok Hcbl)
    $$ [Hview Hlate Hwkv Hrts Hlrd Hidx Hcok]
    as %ws ⟨%kst, %γw, %Hγw, #HisKV, ⟨%rv, #Hrvf, #Hrv⟩, #HhkI, Hkvw, Hwts, Hcok, #Hws, Hwtoks,
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
    as %ast ⟨Hopen, Hhook, %RD, HRDs, #HisReq, #HisAuth⟩
  · iframe #
    iframe Hopen Hhook Hwa Hfa
    ipureintro; exact ⟨Hlgnn, Htpnn, Haufit, Hab⟩
  (try wp_auto)
  -- the compactor is off (`AutoCompactionRetention = 0`)
  rw [Hacr]
  (try wp_auto)
  -- the auth store's reader slots: one for the auth applier, one for the KV's (D14i)
  icases replicate_take1 _ _ hM1 $$ HRDs with ⟨HRD, HRDs⟩
  icases replicate_take1 _ _ (by omega) $$ HRDs with ⟨HRD2, -⟩
  -- `srv.restoreAlarms()`
  rw [show (2 : Nat) = 1 + 1 from rfl]
  icases (ownToks_add 1 1 d.γB.wb).1 $$ Hwb with ⟨Hwb, Hwal⟩
  wp_apply (h32 s cfg.Logger' d (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) qo _
      (DFrac.own 1)) $$ [Hopen Hwal alarmStore be Hfal] as %aerr ⟨Hopen, be, Hares⟩
  · iframe #
    unfold backend.wbTok
    rw [← Hbe0]
    iframe Hopen Hwal alarmStore be Hfal
    ipureintro; exact Hlgnn
  icases Hares with (⟨%Haerr, -⟩ | ⟨%Haerr, %alst, %Halnn, alarmStore, #HalS, Hafr, #Hget, #HalAf⟩)
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
      cfg.WarningApplyDuration' RD (DFrac.own 1) (alarmFresh alst) true) $$ [HRD be Hafr]
    as %ua ⟨be, Hafr, %up, %uopts, %Hua, %Huopts, Hulate⟩
  · iframe #; iframe HRD be Hafr
  -- the alarm store handed over: its apply contract (D14i)
  ihave #HalA := HalAf $$ Hafr
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
  -- the result's ghost state is allocated at the end (`wp_fupd`)
  iapply wp_fupd
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
  have hU64 : ∀ u : Loc, u ↦ (zero_val Perennial.sync.atomic.Uint64) ⊢
      sync.atomic.ownUint64 (GF := GF) u (DFrac.own 1) (W64 0) := by
    intro u; rw [sync.atomic.ownUint64_unseal]; unfold sync.atomic.ownUint64Def; exact .rfl
  have hHalves : ∀ (γg : GName) (n : Nat), ghostVar (GF := GF) γg 1 n ⊢
      ghostVar γg (1 : Qp).half n ∗ ghostVar γg (1 : Qp).half n := by
    intro γg n
    have h := ghostVar_split (GF := GF) γg n (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at h
    exact wand_entails h
  obtain ⟨Hrn1, Hrn2, Hrn3, Hrn4, Hrn5, Hrn6, Hrn7, Hrn8, Hrn9, Hrn10, Hrn11, Hrn12, Hrn13⟩ := Hrnames
  have hγs : envAgree (GF := GF)
      ⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, false, srvFS s, srvCiC γA cil⟩ E₀ :=
    ⟨Hγw.2.2.2.1, Hγw.2.2.2.2, rfl⟩
  -- the transport, started
  ihave #Hts := Htstart $$ Htlive
  iunfold transportStarted at Hts
  icases Hts with ⟨#Htrall, #Htrr⟩
  -- the read names
  iunfold srvReadNamesFresh at Hrd
  icases Hrd with ⟨Hap, Hcm, Hnot, Hlogs, Hpend, Hkst, Hkhi⟩
  icases hHalves _ _ $$ Hkhi with ⟨Hkhi1, Hkhi2⟩
  ihave ⟨Hkvw, #Hcert0⟩ := txn.kvWriter_cert kst γw.st [[], []] $$ Hkvw
  ihave #Hrlb : srvRLogLb ρ.rd.raft [] $$ []
  · iunfold srvRaftLogInv at Hrli
    icases Hrli with ⟨-, #H, -⟩
    iexact H
  -- the indices
  imod (srvIndices_alloc s
      ⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, false, srvFS s, srvCiC γA cil⟩ ρ.rd ⊤
      (by rw [HρRaft]))
    $$ [appliedIndex] [committedIndex] [term] Hap Hcm Hlogs Hpend [] Hrlb
    with ⟨#Hai, Haown, #Hal0, #Hcmi, Hcmown, #Hti⟩
  · iapply hU64; iexact appliedIndex
  · iapply hU64; iexact committedIndex
  · iapply hU64; iexact term
  · simp only [Hlog0]; rw [Hγw.2.2.2.1]; iexact Hcert0
  -- the KV invariants
  imod (kvInv_alloc_boot ρ.rd.raft ρ.rd.kv γ.reCCOk ps bootLog ⊤ (by rw [HρRaft]) (by rw [HρRaft])
      Hrbok (fun ty d h => (Hpol ty d (by rw [HρRaft]; exact h)).2.2) Hc0 Hch0
      (by rw [Hlog0]; simp)) $$ [HrLog] Hkst with ⟨#Hkvinv, Hetcd⟩
  · rw [HρRaft]; iexact HrLog
  imod (kvCertInv_alloc ρ.rd.raft ρ.rd.kv ⊤ (by rw [Hlog0]; simp)) $$ [Hcok] Hkhi1 Hrlb
    with #Hkci
  · rw [Hcok, ← Hγw.2.2.2.2]; iexact Hcok
  -- the mints
  have hργ : ρ.raft.raft = γ := by simp only [ReqNames.raft, HρRaft]
  imod (srvMintInv_alloc ρ ⊤) $$ [Hfresh] [HrdFresh] [HrdCred] with #Hmint
  · rw [hργ]; iexact Hfresh
  · rw [hργ]; iexact HrdFresh
  · rw [hργ, show (2 : Nat) ^ 64 - 2 = (1 + 1) ^ 64 - (1 + 1) from rfl]; iexact HrdCred
  -- `lead`, `leadTimeMu`, `bemu`
  imod (inv_alloc srvN ⊤ iprop(∃ v : w64, sync.atomic.ownUint64 (srvLeadAddr s) (DFrac.own 1) v))
    $$ [lead] with #Hlead
  · inext; iexists W64 0; iapply hU64; iexact lead
  ihave #Hsyncpkg : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  imod sync.init_RWMutex (leadTimeP s) (E := ⊤) (srvLeadTimeMuAddr s) $$ [leadElectedTime] leadTimeMu
    with Hltslots
  · inext; iunfold leadTimeP; iexists _; iexact leadElectedTime
  icases guard_of_slots _ _ $$ Hltslots with ⟨-, #Hltg⟩
  imod sync.init_RWMutex (bemuP s) (E := ⊤) (srvBemuAddr s) $$ [be] bemu with Hbmslots
  · inext; iunfold bemuP; iexists _; iexact be
  icases replicate_take1 _ _ hM1 $$ Hbmslots with ⟨Hbmr, -⟩
  -- the raft node, its transport installed
  ihave #Henv : rnEnvOk (srvEr ρ E₀ (W64 0) (W64 0) bootKV bud) γrn $$ []
  · iapply (rnEnvOk_of_cluster ρ E₀ (W64 0) (W64 0) bootKV bud γrn
      (by rw [Hrn1, hργ]) (by rw [Hrn6]; simp only [ReqNames.raft, HρRaft])
      (by rw [Hrn6]; simp [ReqNames.raft, HρRaft]) (by simp only [ReqNames.raft, HρRaft])
      Hrn4 (by rw [Hrn3, Hrn7]) Hrn2)
    iframe Hkvinv Hrli
    iapply clusterWorkloadOk_of ρ E₀ (W64 0) bootKV
    iframe Hkvinv Hrli Hlogb HNZ0
  imod Hinst $$ %(srvRAddr s) %s %(interface.mkOk (go.GoType.PointerType api.rafthttp.Transport.ty) #t)
    [Henv] [Hcmi] [r] [Htrall] [Hrtm] with ⟨#Hrn, Hrdone, #Hnodef, #Hprop, #Htrf⟩
  · iexact Henv
  · iexact Hcmi
  · iexact r
  · iapply Htrall
  · iexact Hrtm
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  iNamedPrefix Hrn' "N"
  -- the lessor
  ihave #Hlok : lessorOk (lease.lessorIface lp) $$ []
  · iapply lessorOk_of_lessorInv h57 h58 h59 lp γl
    iframe #
  ihave #Hapl : apply.isApplyLessor (lease.lessorIface lp) kst γw.st
      (batchLockInv γA (metaTM d.γB d.P)) #hook $$ []
  · iapply apply.isApplyLessor_of_lessorInv h49 h50 h51 h52 h53 h54 h55 h56 lp kst γw.st
    rw [Hγw.2.1]
    iframe #
    unfold mvcc.storeWT mvcc.storeRT
    rw [Hγw.2.2.1, show mvcc.kbWT (GF := GF) (some d) = backend.wbTok d.γB from rfl,
      show mvcc.kbRT (GF := GF) (some d) = mvcc.bkRTx d.γB d.P d.be from rfl]
    iapply Hlbe $$ Hhook
    ipureintro; exact Hhknn
  ihave #Hast : apply.isAuthStore ast γw.st (batchLockInv γA (metaTM d.γB d.P)) #hook RD false $$ []
  · iapply HisAuth $$ %γw.st %hook [] Hhook
    · ipureintro; exact Hγw.2.2.1
    · ipureintro; exact Hhknn
  -- the persistent fields
  ipersist reqIDGen
  ipersist uberApply
  ipersist memberID
  ipersist firstCommitInTerm
  ipersist errorc
  ipersist compactor
  ipersist stats
  ipersist MaxRequestBytesS
  ipersist ClientCertAuthEnabledS
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨Hlr5, -⟩
  icases replicate_take1 _ _ hM1 $$ Hfcnr with ⟨Hfcr, -⟩
  imodintro
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexists γA, cil, metaTM d.γB d.P,
    (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, false, srvFS s, srvCiC γA cil⟩ : apply.AEnv GF),
    γrn, (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be : GoInterface)
  iframe Hetcd
  isplitr
  · ipureintro; exact ⟨hγs, rfl⟩
  unfold srvBuilt
  iframe HsCI Hloop Happly Hrdone Hcci Hwci Hai Hti Hcmi Hrn
  isplitr
  · -- `#Hfb`
    iexists ⟨cfg.Logger', GoInterface.nil, ua, lease.lessorIface lp, #hook, fcn, alst, bc.cl',
      cfg.QuotaBackendBytes', «$v2_ptr», bc.nodeID', cfg.ElectionTicks', cfg.TickMs'⟩
    unfold srvFieldsBuiltNA srvLeadInv
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro; exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩
  isplitr
  · -- `#Hreqb`
    iexists ⟨gen, GoInterface.nil, cfg.MaxRequestBytes', cfg.ServerFeatureGate',
      cfg.ClientCertAuthEnabled', cfg.ElectionTicks', cfg.TickMs', ast, null, bc.nodeID', bc.cl',
      interface.mkOk (go.GoType.PointerType api.rafthttp.Transport.ty) #t, cid⟩
    unfold srvReqBuilt srvAtomicU64 srvPeersOk
    dsimp only
    rw [Hfgi]
    iframe #
    isplitr
    · have hff : srvFloorFact (GF := GF)
          ⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, false, srvFS s, srvCiC γA cil⟩ =
          srvFloorFact E₀ := by
        funext a b c; unfold srvFloorFact; simp only [Hγw.2.2.2.1]
      rw [hff]; iexact Hgen
    isplitr
    · iunfold srvRaftNode
      iexists rnNodeIface γrn
      iframe Hnodef Hprop
    ipureintro; exact HCfgnn
  isplitr
  · -- `#Hrdb`
    iexists ⟨null, GoInterface.nil, lease.lessorIface lp, ast, cfg.Logger', cfg.WarningApplyDuration',
      null, GoInterface.nil, null, fcn, null⟩
    unfold srvReadBuiltNK
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro; simp
  isplitr
  · -- `#Hrunb`
    iexists ⟨errc, null, null, func.nil, GoInterface.nil, sstats, null⟩
    unfold srvRunBuilt compactorOk
    iframe #
    ileft; ipureintro; rfl
  isplitr
  · -- `#Hsab`
    unfold srvApplyAllBuilt
    iexists _
    iframe NHmsc
    iunfold isRNMsgSnapC at NHmsci
    icases NHmsci with ⟨%γmc, #Hmcb⟩
    iexists γmc, _
    iexact Hmcb
  isplitr
  · -- `#Hkvi`
    unfold srvKVInvs Perennial.named
    iframe #
    ipureintro; exact (Hγw.2.2.2.2.trans Hcok.symm)
  isplitr
  · ipureintro
    refine ⟨?_, rfl⟩
    unfold srvEr
    simp only
    exact (srvC_agree ρ _ E₀ (W64 0) (W64 0) bootKV hγs).symm
  isplitr
  · ipureintro; rfl
  isplitl [w]
  · iexists _; iexact w
  isplitl [applyWait]
  · iexists _; iexact applyWait
  isplitl [done]
  · iexists _; iexact done
  isplitl [stop]
  · iexists _; iexact stop
  isplitl [stopping]
  · iexists _; iexact stopping
  isplitl [ctx]
  · iexists _; iexact ctx
  isplitl [cancel]
  · iexists _; iexact cancel
  isplitl [read]
  · iexists _; iexact read
  isplitl [leaderChanged]
  · iexists _; iexact leaderChanged
  isplitl [SnapshotCountS]
  · iexists _; iexact SnapshotCountS
  isplitl [SnapshotCatchUpEntriesS]
  · iexists _; iexact SnapshotCatchUpEntriesS
  isplitl [wg]
  · iexact wg
  isplitl [wgMu]
  · iexact wgMu
  isplitl [Hcmown]
  · iexists _; iexact Hcmown
  isplitl [Hnot]
  · iexact Hnot
  isplitl [Hthr Happ Hown Hlr5 Hbmr Hrev Haown Hkhi2 forceDiskSnapshot]
  · -- `Happ`
    unfold applyBuiltNA srvBemuReader
    iexists ⟨W64 0, W64 0, W64 0, false⟩, W64 0, W64 0, false
    iframe Hthr Happ Hlr5 Hbmr Haown forceDiskSnapshot
    isplitr
    · ipureintro
      have hm0 := Hci.2
      refine ⟨⟨rfl, ?_⟩, ?_⟩ <;> simp [ciEff, hm0]
    isplitl [Hown]
    · unfold applyBackend
      iframe Hown Hmeta
    isplitl [Hrev]
    · unfold revAuth
      iexists ∅
      iframe Hrev
      ipureintro; intro k hk; simp at hk
    isplitr
    · simp only [bootKV]; rw [← Hlog0]; iexact Hal0
    unfold kvRun kvApplied kvAppliedL kvCert
    iframe Hrlb
    isplitl [Hkhi2]
    · isplitl [Hkhi2]
      · isplitl [Hkhi2]
        · first
            | iexact Hkhi2
            | (simp only [bootKV]; rw [← Hlog0]; iexact Hkhi2)
        isplitr
        · ileft; ipureintro; simp [Hlog0, bootKV]
        ipureintro; simp [kvModel, kvRaftOf_nil, Hlog0, bootKV]
      ipureintro; simp [bootKV, Hch0]
    ipureintro; exact ⟨Hc0, by simp [ReqNames.raft, HρRaft]⟩
  iframe Hlr3 Hlr4
  isplitl [Hfcr]
  · iexists fcn
    iframe firstCommitInTerm Hfcr
  isplitr
  · -- `#Hkv`: the watchable store and its store's read view (`mvcc.New`)
    iexists _, rv
    iframe #
  -- `HWB`: the stores' write budget
  isplitl [Hwts]
  · iexact Hwts
  -- the lifetime premises (D17): `storeSmall` at the store's names (`E₀`'s index names), the id
  -- supply from the time-receipt bound (D19b), the thread bound; `ClusterVersion()` from the cluster's
  -- `Version` contract
  isplitr
  · iapply (storeSmall_of_receipts _ (by omega))
  isplitr
  · iapply (idCred_supply ρ.ids Hrb)
  isplitr
  · icases Hcvm with ⟨%γcv, #Hcvm⟩
    iunfold clusterVersionOk
    iexists γcv
    iintro !> %known %Φ' !> Hk HΦ'
    iapply (h84 s bc.cl' γcv known) $$ [Hk] [HΦ']
    · iframe #; iframe Hk
    inext; iintro %v Hv; iapply HΦ' $$ Hv
  isplitr
  · ipureintro; exact Hbnd
  -- `Hua`: the uber-applier (D14i): its options' contracts, its chain, the apply thread's KV
  have hm0 : γA.m0.1 = W64 0 := by rw [Hci.2]
  have hLoaded : ∀ st : ApplyState, stLoaded γA st = st := by
    intro st; unfold stLoaded; split
    · rename_i h; cases st; simp only at h; subst h; simp [hm0]
    · rfl
  ihave #Hbo : apply.backendOptsOk (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, false, srvFS s, srvCiC γA cil⟩ : apply.AEnv GF) uopts $$ []
  · obtain ⟨Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7, Hu8, Hu9, Hu10, Hu11, Hu12⟩ := Huopts
    iunfold apply.backendOptsOk
    simp only
    rw [Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7, Hu11, Hu12]
    isplitr
    · ipureintro; exact Hlgnn
    isplitr
    · iunfold apply.isApplyKV
      isplitr
      · iexact HisKV
      iexists rv
      iframe Hrvf
      iframe #
    isplitr
    · iapply (mvcc.hookIs_of_init γw.st _ #func.nil d Hγw.2.2.1 hook Hhknn)
      iframe #
    isplitr
    · iexact Hapl
    isplitr
    · iexact Hast
    isplitr
    · iapply HalA $$ %γw.st %hook [] Hhook
      · ipureintro; exact Hγw.2.2.1
      · ipureintro; exact Hhknn
    isplitr
    · iapply Hisc $$ %γw.st %hook [] Hhook
      · ipureintro; exact Hγw.2.2.1
      · ipureintro; exact Hhknn
    isplitr
    · iunfold apply.isRaftStatus
      iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
      isplitr
      · ipureintro; rfl
      isplitr
      · iintro !> !> %Φ' - HΦ'
        iapply (h79 s bc.nodeID') $$ [] [HΦ']
        · iframe #
        inext; iintro -; iapply HΦ'; itrivial
      isplitr
      · iintro !> !> %Φ' - HΦ'
        iapply (h80 s) $$ [] [HΦ']
        · iframe #
          iunfold srvLeadInv; iexact Hlead
        inext; iintro %l -; iapply HΦ'; itrivial
      · iintro !> !> %Φ' - HΦ'
        iapply (h81 s) $$ [] [HΦ']
        · iframe #
        inext; iintro %t' -; iapply HΦ'; itrivial
    isplitr
    · iunfold apply.isSnapshotServer
      iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
      isplitr
      · ipureintro; rfl
      iintro !> !> %Φ' Hfs HΦ'
      iapply (h82 s) $$ [Hfs] [HΦ']
      · iframe #; iframe Hfs
      inext; iintro Hfs; iapply HΦ'; iexact Hfs
    · iunfold apply.isConsistentIndexer
      rw [Hci.1]
      iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩
      isplitr
      · ipureintro; rfl
      iintro !> %C %HC
      obtain ⟨cst, cb, hC, hcp⟩ := HC
      subst hC
      iintro %Φ' !> Hpre HΦ'
      iapply (wp_wand (Φ := fun w => iprop((∀ x : w64,
          iprop(applyThread γA cst ∗ applyBackend γA cil cb) -∗ Φ' #x) ∗
          (⌜w = #(ciEff γA cst.k)⌝ ∗ applyThread γA cst ∗ applyBackend γA cil cb))))
        $$ [Hpre HΦ']
      · iapply (wp_frame_step_l' (by rfl) Std.LawfulSet.subset_refl)
        iframe HΦ'
        icases Hpre with ⟨Hcst, Hcb⟩
        iapply (wp_ci_get h83 γA cil cb cst hcp) $$ [Hcst Hcb]
        · iframe #; iframe Hcst Hcb
        iintro ⟨Hcst, Hcb⟩
        rw [hLoaded]
        iframe Hcst Hcb
        ipureintro; rfl
      · iintro %w ⟨HΦ', %Hw, HP⟩
        subst Hw
        iapply HΦ' $$ HP
  ihave Hul := Hulate $$ %(⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, false, srvFS s, srvCiC γA cil⟩ : apply.AEnv GF) [] Hbo
  · ipureintro; rfl
  icases Hul with ⟨#Hui, %ns, %cr, %Hz, Huo⟩
  obtain ⟨hns, hcr⟩ := Hz trivial
  subst hns hcr
  icases replicate_take1 _ _ (by omega) $$ Hwrds with ⟨Hwrd, -⟩
  iunfold mvcc.watchReader at Hwrd
  icases Hwrd with ⟨Hsrd, -⟩
  iexists ua
  iframe uberApply
  isplitr
  · iunfold apply.applierFor
    iexists up, uopts
    iframe Hui
    ipureintro; exact Hua
  iunfold apply.applyKV
  simp only [bootKV]
  iexists up
  isplitr
  · ipureintro; exact Hua
  isplitl [Huo]
  · iexact Huo
  iunfold apply.kvOwn
  iframe Hsrd Hkvw HRD2
  iunfold apply.leasesLive
  iexists []
  isplitr
  · iunfold txn.leasesKnown; simp [mvcc.stateAfter, txn.leasesOk]
    iintro !> %l %h
    obtain ⟨a, ha, -⟩ := h
    simp [mvcc.applyChanges] at ha
  iunfold lease.lessorUser
  rw [Hγw.2.1]
  iframe Hlown Hlrd2

end proof

end EtcdGrove
end Perennial
