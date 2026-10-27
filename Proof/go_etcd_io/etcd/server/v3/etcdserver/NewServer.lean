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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NetBridge
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- `bemu`'s resource is fractional (for `sync.init_RWMutex`); (D22 receiver epochs, S7b) the
witnesses agree by the current backend's ghost variable. -/
instance bemuP_fractional (s : Loc) (γbe : GName) : Fractional (bemuP (GF := GF) s γbe) := by
  unfold bemuP
  have h1 : ∀ d : mvcc.KBReal, Fractional (fun q : Qp =>
      iprop(srvBeAddr s ↦{DFrac.own q.half} srvBeIface d.be)) := fun d =>
    ⟨fun q1 q2 => by
      rw [show (q1 + q2).half = q1.half + q2.half from Subtype.ext (by grind)]
      exact (fractional_of_dfractional
        (fun dq => typedPointsto (GF := GF) (srvBeAddr s) (srvBeIface d.be) dq)).fractional
          q1.half q2.half⟩
  have h2 : ∀ d : mvcc.KBReal, Fractional (fun q : Qp =>
      dghostVar (GF := GF) γbe (DFrac.own q.half) d) := fun d =>
    ⟨fun q1 q2 => by
      rw [show (q1 + q2).half = q1.half + q2.half from Subtype.ext (by grind)]
      exact (dghostVar_fractional (GF := GF) γbe d).fractional q1.half q2.half⟩
  have h3 : ∀ d : mvcc.KBReal, Fractional (fun _ : Qp => srvBeRO (GF := GF) d) := fun d =>
    persistent_fractional
  exact fractional_exists_agree
    (fun (d : mvcc.KBReal) q => iprop(srvBeAddr s ↦{DFrac.own q.half} srvBeIface d.be ∗
      dghostVar γbe (DFrac.own q.half) d ∗ srvBeRO d))
    (fun d => @fractional_sep _ _ _ _ (h1 d) (@fractional_sep _ _ _ _ (h2 d) (h3 d)))
    (fun x y q1 q2 => by
      iintro ⟨⟨-, H1, -⟩, ⟨-, H2, -⟩⟩
      iapply dghostVar_agree γbe x _ y _ $$ H1 H2)

/-- `time.Duration(ttl) * time.Second` is positive for a TTL in `(0, 2 ^ 32)` seconds. -/
theorem tokenTTL_pos (x : w64) (h1 : 0 < uint.Z x) (h2 : uint.Z x < 2 ^ 32) :
    0 < sint.Z (x * W64 1000000000) := by
  have hm : uint.Z (x * W64 1000000000) = uint.Z x * 1000000000 := by word
  have hlt : uint.Z (x * W64 1000000000) < 2 ^ 63 := by rw [hm]; omega
  have hpos : 0 < uint.Z (x * W64 1000000000) := by rw [hm]; omega
  generalize x * W64 1000000000 = y at hlt hpos
  word

-- (2026-10-22) the unused-variables linter walks the proof's info tree: 30s of this module's
-- CPU (on the build's critical path)
set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option pp.maxSteps 200000 in
set_option maxHeartbeats 0 in
theorem NewServer.wp_proofM (on : Bool)
    -- `int64(f)`'s semantics (`FloatToInt.lean`: a hypothesis on the semantics, as `go.Semantics`)
    [Float64ToInt64Semantics]
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
    (hTP : authSrvTP (GF := GF) (hG := hG) on)
    (h26 : mvcc.New.spec (GF := GF) (hG := hG))
    (h27 : newCorruptionChecker.spec (GF := GF) (hG := hG))
    (h28 : mvcc.store.HashStorage.spec (GF := GF) (hG := hG))
    (h29 : schema.NewAuthBackend.spec (GF := GF) (hG := hG))
    (h31 : v3compactor.New.spec (GF := GF) (hG := hG))
    (h32 : EtcdServer.restoreAlarms.spec (GF := GF) (hG := hG))
    (h33 : EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG))
    (h34 : EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (h35 : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (h36 : config.ServerConfig.PeerDialTimeout.spec (GF := GF) (hG := hG))
    (h37 : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (h38 : rafthttp.Transport.Start.spec (GF := GF) (hG := hG))
    (h39 : rafthttp.Transport.AddRemote.spec (GF := GF) (hG := hG))
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
    (h84 : EtcdServer.ClusterVersion.spec (GF := GF) (hG := hG))
    (h85 : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (h86 : node.ApplyConfChange.spec (GF := GF) (hG := hG))
    -- (D21 M2) the inbound path: raft's `Step` and reports, the server's `Process` and co.
    (h87 : node.Step.spec (GF := GF) (hG := hG))
    (h88 : node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h89 : node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (h90 : EtcdServer.Process.spec (GF := GF) (hG := hG))
    (h91 : EtcdServer.IsIDRemoved.spec (GF := GF) (hG := hG))
    (h92 : EtcdServer.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h93 : EtcdServer.ReportSnapshot.spec (GF := GF) (hG := hG))
    -- (leases T3, 2026-10-25) the backend's delete, for the lessor's in the store's contract
    (h94 : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG)) :
    NewServer.specM (GF := GF) (hG := hG) on := by
  intro cfg U γ bud id bootLog ρ E₀ N Φs γn dir γd HρRaft Hpol Hc0 Hch0 Hlog0 Hcok Hlgnn Hcbl Hacr
    Hbnd Hrb HrbN HrbS Hboot Hpfx HΦs Hfgp Hdirok HpU Hauthcfg
  wp_start
  iNamed Hpre
  -- (D19r (C)) the raft status's mutex, from the package's facts
  ihave #Hrs : rnRaftStatusOk (GF := GF) $$ []
  · ihave Hsi0 : (srvInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    iunfold srvInit at Hsi0
    icases Hsi0 with ⟨⟨-, -, -, -, -, -, -, #HRS⟩, -⟩
    iunfold rnRaftStatusOk
    iexact HRS
  -- (D19r (D)) `closec` closed, from `pkg/wait`'s facts
  ihave #Hwci : waitClosecInit (GF := GF) $$ []
  · iapply waitClosecInit_of_pkg
    iPkgInit
  wp_apply wp_with_defer as %defer defer
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hboot' := Hboot
  iunfold bootstrapContract at Hboot'
  wp_apply Hboot' $$ [Hrauth] as %b %err Hb
  · iframe; iframe Hcfgro
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
  wp_apply h7 $$ [$nodeID] as %ids ⟨nodeID, -⟩
  wp_apply h6 as %lstats ⟨%Hlsnn, #Hlsi, Hlsf⟩
  (try wp_auto)
  -- the server's literal: `readych`, `lgMu`, `errorc`, the raft wrapper
  wp_apply chan.wp_make1 (V := Unit) as %rdc %γrdc ⟨#Hrdc, %Hrdcap, Hrdo⟩
  (try wp_auto)
  wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %errc %γec ⟨#Herrc, %Herrcap, Herro⟩
  · ipureintro; word
  -- `errorc`: nothing is sent on it in the runs covered (D19m)
  imod start_bag (V := GoInterface) (fun _ => iprop(False)) _ errc γec (by trivial) $$ Herrc Herro
    with #Herrb
  (try wp_auto)
  -- `b.raft.newRaftNode(b.ss, b.storage.wal.w, b.cluster.cl)`: raft's node started
  -- (`NodeStartSpec`, `raftNode_of_StartNode`)
  have hNS := raftNode_of_StartNode (GF := GF) (MemStorReg.memStorRegName GF) h8 h9 h10 h11 h12 h87 h88 h89 h78
    h86
  obtain ⟨Hrlg, Hrhb, Hrvalid, Hrlok, Hrstor, Hrinfl, Hrdpf, Hrro, Hrdccv, Hrsizes, Hrasync,
    Hrapplied, Hrid, Hrps, Hrpsne, Hrnodup, Hr0, Hrpslen, Hrmem, Hrcfg, Hrboot, Hrbok⟩ := Hraft
  -- (D22 S-b′3) the storage's certificate link: the no-snapshot mode's
  ihave #Hclk : certLink (GF := GF) γ (memStorIface bv.storage') $$ []
  · iapply certLink_noSnap; exact Hnosnap.1
  -- (rafthttp stage 6d) the raft loop's key to the transport's `Send` (`srvTrKey`), its name
  -- allocated now: the raft node's environment is built before the transport
  imod (srvSendKey_alloc (GF := GF)) with ⟨%γk, Hk⟩
  ihave #Htkok' : rnTickerOk (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) bud id (srvTrKey γn γk)) $$ []
  · iapply rnTickerOk_srvErM_S $$ Htkok
  -- (D43 M3) raft's static mode: the servers' (`bootInit`'s static case is the ghost state)
  ihave Hghost : bootInit γ .static id (GMap.listToSet ps) bootLog $$ [Hghost]
  · unfold bootInit; iexact Hghost
  wp_apply (hNS (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) bud id (srvTrKey γn γk)) γ .static bud bs.raft' bs.ss' bw.w' bc.cl'
    (DFrac.own 1) bv cv lok γs pv ps ctxs bootLog Hrlg Hrhb Hrvalid Hrlok Hrstor Hrinfl Hrdpf
    Hrro Hrdccv Hrsizes Hrasync Hrapplied Hrps Hrpsne Hrnodup Hr0 Hrpslen Hrmem Hrcfg Hrboot
    Hrbok (fun _ _ _ _ h => by cases h) (by simp [srvErM, HρRaft]) (by simp [srvErM, HρRaft]) (by simp [srvErM, HρRaft])
    (by simpa [srvErM] using Hpol) (fun _ => by rw [Hnosnap.2]; exact Int.le_refl _))
    $$ [Hbv Hc Hstor Hpeers Hghost Htok]
    as %r ⟨%γrn, %rvr, %Hrnames, Hr, Hrtm, #HstepI, Hloop, Happly, #Hrli, Hinst, Hbv, Hpeers, Htok⟩
  · iframe Hbv Hc Hstor Hpeers Htok
    rw [Hrid]
    iframe Hghost
    iframe Hclk Hcl Hmarshal Hctx Hinit Hsi Hreg Hlok Hrs Hstop Hns Htkok' Htdok Hsetlg Hzap HtermLB Hbud Hcinv Hcomm
    iintro %γw' %hw
    -- (D19b stage 5) the run's premise on the `Ready`s, from the receipt bound
    iunfold rnLogFits
    ipureintro; rw [hw.1]; omega
  (try wp_auto)
  -- the configuration, field by field from here on
  iStructNamed cfg
  ihave %HcuNN := typedPointsto_not_null _ _ _ $$ ClientURLs
  wp_apply h13 as %cus -
  · ipureintro; exact HcuNN
  (try wp_auto)
  -- the request ids' generator, the notifiers
  ihave #Hipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil $$ []
  · iPkgInit
  ihave #Hnpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  wp_apply time.wp_Now as %now -
  -- (D21e (A), stage M4) over the cluster's claims, at the member's prefix
  wp_apply (h14 ρ.ids _ now Φs (by rw [Hpfx]; congr 1; rw [← Hid])) $$ [Hids] as %gen #Hgen0
  · iframe Hidc; iframe Hids
  ihave #Hgen : idGen ρ.ids gen (srvFloorFact E₀) $$ []
  · rw [← HΦs]; iexact Hgen0
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
  icases Hsi with ⟨⟨-, -, -, -, -, ⟨%gvf, #Hgvf, %Hgvfl⟩, ⟨%gvi, #Hgvi, %Hgvil⟩, -⟩, -⟩
  (try wp_auto)
  wp_apply h16 $$ []
  · iframe Hgvf Hfg; ipureintro; exact Hfgp
  ihave #Hppkg : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply h7 $$ [$nodeID] as %ids2 ⟨nodeID, %Hids2⟩
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %lbl Hlbl
  wp_apply wp_mapInsert go.string lbl _ _ _ $$ [$Hlbl] as Hlbl
  (try wp_auto)
  wp_apply h17 gvi lbl [go!"server_id"] _ _ $$ [Hlbl] as %gsi ⟨%gi, %Hgi, #Hgset, -⟩
  · iframe #; iframe Hlbl; ipureintro
    exact ⟨Hgvil, prometheus.labelMapOk_one _ _ (utf8Valid_of_ascii _ (Hids2 ▸ types.idStr_ascii _))⟩
  subst Hgi
  (try wp_auto)
  wp_apply Hgset
  (try wp_auto)
  -- (audit B4a) the cluster's `versionChanged` field, owned, then read-only
  wp_apply h18 $$ [Hvcn] as Hvcn
  · iframe Hrc; iframe Hvcn
  ipersist Hvcn
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
  have hMR : 2 ^ 29 + 2 ^ 23 + 2 ^ 22 + 100 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  have hM1 : 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by omega
  -- (D21 M2; rafthttp stage 6d) the transport's `lgMu` reader slots, one per concurrent call into
  -- the server's `Raft` (`Process`'s `Logger()`): `httpProcSlots` for the requests the member's raft
  -- handler serves, `2 ^ 23` for the peers' goroutines (eight each, at most `2 ^ 20` peers)
  have hHP : http.httpProcSlots = 2 ^ 29 := rfl
  icases replicate_takeN _ http.httpProcSlots _ (by omega) $$ Hlgrs with ⟨HlgServe, Hlgrs⟩
  icases replicate_takeN _ (2 ^ 23) _ (by omega) $$ Hlgrs with ⟨HlgPeers, Hlgrs⟩
  -- (D22 J-T) `2 ^ 22` for the transport's pool: four for each other member's one remote
  icases replicate_takeN _ (2 ^ 22) _ (by omega) $$ Hlgrs with ⟨HlgPool, Hlgrs⟩
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨Hlr1, Hlgrs⟩
  wp_apply h19 $$ [Hlr1] as ⟨-, Hlr1⟩
  · iframe lg; iframe Hlr1; ipureintro; exact Hlgnn
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
  wp_apply Hen $$ [] as %ckpp -
  · ipureintro; simp [serverFeatures]
  (try wp_auto)
  wp_apply h20 $$ [] as %reqto -
  · iframe TickMsS ElectionTicksS
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
  ihave ⟨#HB, #HSC, Hhook, Hopen, Hview, Hwb, Hrbo, Hrts⟩ := bootBackend_of_newPost d.γB d.P
    (fun _ => mvcc.lateW d.gx) (fun γB => batchLockInv γA (metaTM γB d.P)) d.be D N HD HN $$ Hnew
  rw [show N + 7 = (N + 6) + 1 by omega]
  icases ownToks_add_1 1 (N + 6) d.γB.wb $$ Hwb with ⟨Hwb, Hwl⟩
  -- `lease.NewLessor`
  rw [Hbe0]
  -- the grant guard `False` (`srvGrantGuard`, D19n, D45): the lessor's `expiredC` never delivers
  -- (D22, 2026-10-23) the rest buckets: the tracked buckets' half, at the fresh file's
  have hDl : ∀ n ∈ mvcc.restBuckets, ((backend.rbData d.P D).lookup n).getD ∅ = ∅ :=
    fun n hn => by rw [rbData_real_lookup d D n hn]; exact HDr.1 n hn
  wp_apply (h24 cfg.Logger' _ _ d (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) (1 : Qp).half
      (srvGrantGuard) (backend.rbData d.P D))
    $$ [Hopen Hwl Hrbo]
    as %l ⟨Hopen, Hrbo, %lp, %γl, %Hl, #Hlinv, #Hlcfg, #Hlexp, -, Hlrd, Hlown, Hlrvk, Hro, #Hlck, HleOn, #Hlbe, #Hllk⟩
  · iframe HB Hclok
    unfold backend.wbTok
    iframe Hopen Hwl Hrbo
    ipureintro; exact ⟨Hlgnn, Hckok, by simp, hDl go!"lease" (by decide)⟩
  (try wp_auto)
  -- `auth.NewTokenProvider`
  ihave #Hapkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  wp_func_lits
  wp_apply hTP as %tp %terr ⟨%Htp, Hkit⟩
  · ipureintro
    exact ⟨Hlgnn, fun hon => ⟨(Hauthcfg hon).1,
      tokenTTL_pos _ (Hauthcfg hon).2.1 (Hauthcfg hon).2.2⟩⟩
  clear Hauthcfg
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
  -- (the auth plan's E2i) the auth mode and the auth store's construction in it
  ihave Hkit := Hkit $$ []
  · ipureintro; rfl
  -- (the mode's equation kept in the Iris context: `word` would substitute `on` in the Lean one)
  imod Hkit with ⟨%M, #HM, Hkit⟩
  iunfold authStoreKit at Hkit
  icases Hkit with ⟨%K, HK, #HKt⟩
  (try wp_auto)
  -- `mvcc.New`: the watchable store over the real backend (`server_kv_watchable_of`)
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨Hlr2, Hlgrs⟩
  wp_apply h19 $$ [Hlr2] as ⟨-, Hlr2⟩
  · iframe lg; iframe Hlr2; ipureintro; exact Hlgnn
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
  wp_apply (lc := 2) (server_kv_watchable_of h26 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73
      h74 h75 h76 h77 h94 h46 h47 h48 cfg.Logger' (lease.lessorIface lp) _ d HbP E₀.γ.bucket γl
      (batchLockInv γA (metaTM d.γB d.P)) #func.nil func.nil N E₀.γ.idx E₀.γ.cok M Hcbl Hrb)
    $$ [Hview Hncmp Hlate Hwkv Hrts Hlrd Hro Hidx Hcok]
    as %ws ⟨%kst, %γw, %Hγw, #HisKV, ⟨%rv, #Hrvf, #Hrv⟩, #HhkI, Hkvw, Hwts, Hcok, #Hws, Hwtoks,
      Hwrds, Hwcl, Hret0, -, #Htag⟩
  · ihave #Hsz0 : mvcc.keySized (GF := GF) d.γB d.P d.be $$ []
    · iapply Hsz
    iframe Hisl HB Hsz0
    iframe Hview Hncmp Hlate Hwkv Hrts Hlrd Hro Hidx Hcok
  -- (D19g (b)) the store's reader slots for request goroutines
  icases replicate_takeN _ 64 _ (by omega) $$ Hwrds with ⟨Hwsr, Hwrds⟩
  -- (2026-10-20, watchkv) 64 more for the watch service's run slots (`srvWatchReaders`)
  icases replicate_takeN _ 64 _ (by omega) $$ Hwrds with ⟨Hwrx, Hwrds⟩
  ihave Hsrs := replicate_mono _ (mvcc.storeReader kst γw.st) 64
    (by unfold mvcc.watchReader; iintro ⟨H, -⟩; iexact H) $$ Hwsr
  (try wp_auto)
  ihave #Hws' := Hws
  iunfold mvcc.isWatchableStore at Hws'
  icases Hws' with ⟨%wvc, %wstc, %wrv, %wγv, Hws'⟩
  iNamed Hws'
  -- (D22 receiver epochs, S5a) two of the store's readers retired for backend tokens of their own
  -- (`mvcc.storeReader_retire`): the storage version monitor's and the apply thread's (its
  -- `mvcc.writerOwn`, in `apply.kvOwn`: its writes under the batch lock borrow one)
  icases replicate_take1 _ _ (by omega) $$ Hwrds with ⟨HwrSV, Hwrds⟩
  icases replicate_take1 _ _ (by omega) $$ Hwrds with ⟨HwrA, Hwrds⟩
  iunfold mvcc.watchReader at HwrSV HwrA
  icases HwrSV with ⟨HwrSV, -⟩
  icases HwrA with ⟨HwrA, -⟩
  -- (S5b) at the writer's fragment (`kvWriter`'s), a pin of the current names
  iunfold txn.kvWriter at Hkvw
  icases Hkvw with ⟨Hkvw0, Hkvw1, Hfrag0⟩
  iunfold mvcc.writerFrag at Hfrag0
  icases Hfrag0 with ⟨%ow, Hpinw⟩
  imod mvcc.storeReader_retire kst γw.st _ ow 0 $$ Hlc1 Hs Hpinw HwrSV Hret0
    with ⟨HrtSV, Hret1, Hpinw⟩
  imod mvcc.storeReader_retire kst γw.st _ ow 1 $$ Hlc2 Hs Hpinw HwrA Hret1 with ⟨HrtA, HtrA, Hpinw⟩
  ihave Hkvw : txn.kvWriter kst γw.st [[], []] $$ [Hkvw0 Hkvw1 Hpinw]
  · iunfold txn.kvWriter; iframe Hkvw0 Hkvw1; iunfold mvcc.writerFrag; iexists ow; iexact Hpinw
  -- (D22 receiver epochs, S7b) the current backend's ghost variable, at the real backend: half
  -- `bemu`'s lock invariant's, a quarter the apply thread's, a quarter the write budget's
  imod (dghostVar_alloc (GF := GF) d) with ⟨%γbe, Hγbe⟩
  icases (dghostVar_split (GF := GF) γbe d (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half))
    $$ [Hγbe] with ⟨Hγbm, Hγbe⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hγbe
  icases (dghostVar_split (GF := GF) γbe d (DFrac.own (1 : Qp).half.half)
      (DFrac.own (1 : Qp).half.half)) $$ [Hγbe] with ⟨HγbA, HγbW⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hγbe
  -- `newCorruptionChecker(lg, srv, srv.kv.HashStorage())`
  rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty)
    (m := go!"HashStorage")]
  wp_call
  (try wp_auto)
  wp_apply h28 $$ [] as %hst -
  · iframe Hs
  wp_apply h27 as %cc -
  (try wp_auto)
  -- `auth.NewAuthStore(srv.Logger(), schema.NewAuthBackend(srv.Logger(), srv.be), tp, …)`
  icases replicate_take2 _ _ (by omega) $$ Hlgrs with ⟨Hlr3, Hlr4, Hlgrs⟩
  wp_apply h19 $$ [Hlr3] as ⟨-, Hlr3⟩
  · iframe lg; iframe Hlr3; ipureintro; exact Hlgnn
  wp_apply h19 $$ [Hlr4] as ⟨-, Hlr4⟩
  · iframe lg; iframe Hlr4; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply h29 as %ab ⟨%abl, %Hab, #Hablg, #Habbe⟩
  (try wp_auto)
  rw [show (4 : Nat) = 2 + 2 from rfl]
  icases (ownToks_add 2 2 d.γB.wb).1 $$ Hwb with ⟨Hwb, Hwa⟩
  ihave HKt' := HKt $$ %cfg.Logger' %ab %abl %d %(mvcc.lateW d.gx)
    %(batchLockInv γA (metaTM d.γB d.P)) %(1 : Qp).half %((backend.rbData d.P D).insert go!"lease" ∅)
  wp_apply HKt'
    $$ [HK Hopen Hhook Hwa Hrbo]
    as %ast ⟨Hopen, Hhook, Hrbo, %RD, %astl, %Hastl, HauthOn, HRDs, #HisReq, #HisAuth,
      #HstL, #HstLb, #HstPub, HAres, #HauR⟩
  · iframe Habbe Hablg HB
    iframe Hapkg HK Hopen Hhook Hwa Hrbo
    ipureintro
    refine ⟨Hlgnn, Htpnn, Haufit, Hab, ?_, ?_, ?_⟩
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hDl go!"auth" (by decide)
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hDl go!"authUsers" (by decide)
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hDl go!"authRoles" (by decide)
  (try wp_auto)
  -- (E3u) the start's auth state published, for the applied index's invariant
  imod authApplyResPre_publish M astl _ _ $$ HstPub HAres with ⟨HAres, #Hpub0⟩
  -- the compactor is off (`AutoCompactionRetention = 0`)
  rw [Hacr]
  (try wp_auto)
  -- the auth store's reader slots: one for the auth applier, one for the KV's (D14i)
  icases replicate_take1 _ _ hM1 $$ HRDs with ⟨HRD, HRDs⟩
  icases replicate_take1 _ _ (by omega) $$ HRDs with ⟨HRD2, HRDs⟩
  -- (D19g (b)) the auth store's reader slots for request goroutines
  icases replicate_takeN _ 64 _ (by omega) $$ HRDs with ⟨HRDs, HRDstock⟩
  -- `srv.restoreAlarms()`
  rw [show (2 : Nat) = 1 + 1 from rfl]
  icases (ownToks_add 1 1 d.γB.wb).1 $$ Hwb with ⟨Hwb, Hwal⟩
  wp_apply (h32 s cfg.Logger' d (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) (1 : Qp).half _
      (DFrac.own 1) (((((backend.rbData d.P D).insert go!"lease" ∅).insert go!"auth" authBoot).insert
        go!"authUsers" ∅).insert go!"authRoles" ∅))
    $$ [Hopen Hwal alarmStore be Hrbo] as %aerr ⟨Hopen, Hrbo, be, Hares⟩
  · iframe #
    unfold backend.wbTok
    rw [← Hbe0]
    iframe Hopen Hwal alarmStore be Hrbo
    ipureintro
    refine ⟨Hlgnn, ?_⟩
    rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
      GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide)]
    exact hDl go!"alarm" (by decide)
  -- the rest buckets after the constructors: the boot state's
  rw [restBootBk_of_fresh d D HDr]
  clear hDl HDr
  icases Hares with (⟨%Haerr, -⟩ | ⟨%Haerr, %alst, %Halnn, alarmStore, #HalS, HalOn, Hafr, #Hget, #HalAf⟩)
  · -- the alarms could not be restored: the error returned, the store and `b` closed
    cases aerr with
    | nil => exact absurd rfl Haerr
    | ok ei => ?_
    wp_auto
    wp_apply h42 $$ [Hwcl]
    · iframe Hws; iframe Hwcl
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
      cfg.WarningApplyDuration' RD (DFrac.own 1) (alarmFresh alst) true Hbuq) $$ [HRD be Hafr]
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
  · iframe ServerFeatureGateS Hfg; ipureintro; simp [serverFeatures]
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
    iframe consistIndex Hcons HisCI
  wp_apply (h34 s γA cil (metaTM d.γB d.P)) as %hook ⟨%Hhknn, #Hhks⟩
  · iframe HsCI
  (try wp_auto)
  wp_apply (h35 d.γB d.P (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) d.be (1 : Qp).half func.nil hook)
    $$ [Hopen Hhook Hwb] as ⟨Hopen, Hhook⟩
  · iframe HB
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
  · iframe TickMs ElectionTicks
  (try wp_auto)
  wp_apply h37 as -
  · iframe Hcid
  (try wp_auto)
  obtain ⟨Hrn1, Hrn2, Hrn3, Hrn4, Hrn4d, Hrn5, Hrn5n, Hrn6, Hrn7, Hrn8, Hrn9, Hrn10, Hrn11, Hrn12, Hrn13,
    Hrn14, Hrn15⟩ :=
    Hrnames
  -- (D21 M2) what the transport's calls into the server read (`srvProcOk`): the wrapper's
  -- fixed fields split off its struct (the node's among them), the member id, the stats
  imod rnFixed_split (srvRAddr s) rvr $$ r with ⟨#Hfix, Htrf, HlatestTs⟩
  ihave #HNodeC : rnNodeAddr (srvRAddr s) ↦□ rnNodeIface γrn $$ []
  · rw [← Hrn14]
    iunfold rnFixed at Hfix
    iNamed Hfix
    iexact NodeC
  ipersist memberID
  ipersist beHooks
  ipersist stats
  ihave #Hprocok : srvProcOk γn s id $$ []
  · iunfold srvProcOk
    iexists cfg.Logger', bc.cl', sstats, γrn
    rw [← Hid]
    iframe stats memberID HNodeC cluster lg HstepI Hrc
    ipureintro
    have hb : γrn.node.raft.reBoot ≠ [] := by
      rw [Hrn1, Hrboot]
      intro h
      have hl := Hrbok.1
      rw [h] at hl
      exact Hrpsne (List.length_eq_zero_iff.mp hl.symm)
    exact ⟨Hlgnn, by rw [Hrn5, Hrid, Hid], Hssnn, by rw [Hγn.1, Hrn1, Hrn2],
      by rw [Hrn1]; exact Hnosnap.1, hb, by rw [Hrn1]; exact Hnoxfer⟩
  -- (D22 S-i) the member's snapshot directory, empty (a fresh data directory), for the
  -- transport's snapshot handler; no removal yet (`applySnapshot`'s, S-j); (2026-10-26, D22 J2) at
  -- the names raft's names give the member (`RaftNames.reSnapLoc`, `snapDir_init`)
  -- (2026-10-26, D22 J1a) with the server's removal fact (`srvSnapRm`, J0 item 3), over the
  -- snapshot-taken counter `γt`, allocated here at `0` for the apply thread
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γt, Hγt, -⟩
  imod (snapDir_init bs.ss' γd γn.N.img (srvSnapRm γt ρ.rd) ⊤) $$ Hsdir with #Hsdir
  ihave #Hnro := srv_netRaftOk h90 h91 h92 h93 γn γd s id $$ [$Hpkg $Hprocok]
  generalize htr : «$r0_ptr» = t
  -- (rafthttp stage 6d) the member's URLs, read-only; it is a member of the directory (raft's peer)
  ihave #HpU : cfg.PeerURLs' ↦*□ U.peer $$ []
  · iunfold bootCfgRO at Hcfgro
    icases Hcfgro with ⟨#H, -⟩
    iexact H
  have Hdid : γn.dir id ≠ [] := by
    rw [Hγn.2]; exact (Hdirps.1 id).2 (Hrid ▸ Hrmem)
  -- (D22 J-T, 2026-10-27; D43 M5c until then: no pool, the transport frozen) the transport's pool
  -- of `R`s: four for each other member (`ps.filter (· ≠ id)`), the one remote a handler may add
  -- for it (W8: a member not a peer between the snapshot path's `RemoveAllPeers` and `AddPeer`s)
  have HLnd : (ps.filter (· ≠ id)).Nodup := Hrnodup.filter _
  have HLmem : ∀ f, f ∈ ps.filter (· ≠ id) ↔ f ∈ ps ∧ f ≠ id := by
    intro f; simp [List.mem_filter]
  have HLlen : 4 * (ps.filter (· ≠ id)).length ≤ 2 ^ 22 := by
    have := List.length_filter_le (· ≠ id) ps
    have h2 := Hdirps.2
    omega
  ihave HRL := replicate_list4 (srvLgReader s) (ps.filter (· ≠ id)) (2 ^ 22) HLlen $$ HlgPool
  have Hturls : trURLsOk (netRh γn) id U.peer :=
    trURLsOk_of_dir γn dir Hγn.2 Hdirok ps Hdirps.1 id (Hrid ▸ Hrmem) U.peer HpU
  wp_apply (h38 γn t _ (srvLgReader s) γd (srvSnapRm γt ρ.rd) U.peer (ps.filter (· ≠ id)))
    $$ [«$r0» Hlsf HRL] as %terr Htres
  · iframe «$r0»
    simp only
    rw [Hid]
    iframe Hnro Hss Hsdir HpU Hnet Hlsi Hlsf HRL
    ipureintro; refine ⟨Hlgnn, Hssnn, Hlsnn, ?_, Hdid, HLnd, Hturls⟩ <;> first | rfl | trivial
  icases Htres with (%Hterr | ⟨%Hterr, %c, %Hc, Htlive, Hun, Htoks, #HtrNet, #Htrr, -⟩)
  · -- the transport could not start: the error returned, the store and `b` closed
    cases terr with
    | nil => exact absurd rfl Hterr
    | ok ei => ?_
    wp_auto
    wp_apply h42 $$ [Hwcl]
    · iframe Hws; iframe Hwcl
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
  · -- (the partition plan's S1, 2026-10-20) no remotes (`bootOk`'s `Hrms0`: a new cluster's
    -- bootstrap), so the loop's body is dead: `AddRemote` is never called, and the transport's
    -- list of remotes stays `[]` (`transportRemotes t []`, for `srvNetMember`)
    exfalso
    have Hlen : rms.length = 0 := by rw [Hrms0]; rfl
    unfold sint.nat at Hrmsl
    word
  -- `for _, m := range b.cluster.cl.Members() { … tr.AddPeer(…) }`: (D21 M2) the members'
  -- records, each naming its member's own URLs (`bootOk`'s `Hmembers`, the directory `dir`)
  wp_apply Hmembers as %msl %mps %Hmps Hmsl Hmso
  ihave %Hmsll := ownSlice_len _ _ _ $$ Hmsl
  simp only [List.length_map] at Hmsll
  have Hpsl : mps.length ≤ 2 ^ 20 := by
    have h := congrArg List.length Hmps
    simp only [List.length_map] at h
    omega
  obtain ⟨Hcl, Hcd, HcR, HcL⟩ := Hc
  simp only at Hcl
  rw [Hid] at Hcl
  -- (rafthttp stage 6d) the loop's invariant: the ids `AddPeer` was called for (`L`, with the
  -- transport's live state), each other member's so far, and `lgMu`'s reader slots left for the
  -- next peers (eight each)
  ihave IH2 : iprop(∃ (n : w64) (mm : Loc) (L : List w64), "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mm ∗
      "Htlive" ∷ trLive γn t c L ∗ "Hun" ∷ trUnopened c ∗ "Hnr" ∷ trNoRemAcc c L ∗
      "HlgPeers" ∷ ([∗list] _x ∈ List.replicate (2 ^ 23 - 8 * L.length) (), srvLgReader s) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z msl.len ∧ L.length ≤ (sint.Z n).toNat⌝ ∗
      "%Hcov" ∷ ⌜∀ (k : Nat) (p : Loc × w64), k < (sint.Z n).toNat → mps[k]? = some p →
        p.2 ≠ id → p.2 ∈ L⌝) $$ [i m Htlive Hun HlgPeers]
  · iexists W64 0, _, []
    iframe i m Htlive Hun
    isplitr
    · iapply trNoRemAcc_nil
    isplitl [HlgPeers]
    · rw [show 2 ^ 23 - 8 * ([] : List w64).length = 2 ^ 23 from rfl]
      iexact HlgPeers
    ipureintro
    refine ⟨⟨by decide, by have := Hmsll.2; word, by simp⟩, fun k p hk _ _ => ?_⟩
    exact absurd hk (by simp)
  -- the result's ghost state is allocated at the end (`wp_fupd`)
  iapply wp_fupd
  -- the loop gets what it reads only (`wp_for` generalizes the whole context into its invariant,
  -- and `wp_for_post` reframes it at every iteration); the rest waits after it, with the ids added
  wp_join (iprop(∃ (L : List w64),
      "b" ∷ b_ptr ↦ b ∗ "Hb" ∷ b ↦ bs ∗
      "nodeID" ∷ bs.cluster'.[bootstrappedCluster, go!"nodeID"] ↦ bc.nodeID' ∗ "tr" ∷ tr_ptr ↦ t ∗
      "Hmsl" ∷ msl ↦* List.map Prod.fst mps ∗
      "Hmso" ∷ ([∗list] p ∈ mps, memberDirIs dir p.fst p.snd) ∗
      "Htlive" ∷ trLive γn t c L ∗ "Hun" ∷ trUnopened c ∗ "Hnr" ∷ trNoRemAcc c L ∗
      "%Hcov" ∷ ⌜∀ f, (netRh γn).member f → f ≠ id → f ∈ L⌝))
    at (App (App (App (Val doFor) _) _) _) with [b Hb nodeID tr Hmsl Hmso IH2]
    as ⟨%L, b, Hb, nodeID, tr, Hmsl, Hmso, Htlive, Hun, Hnr, %Hcov⟩
  · wp_for IH2
    wp_if_destruct
    · obtain ⟨px, Hpx⟩ : ∃ px, mps[(sint.Z n).toNat]? = some px :=
        ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hmsll; word)⟩
      have Hmx : (mps.map Prod.fst)[(sint.Z n).toNat]? = some px.1 := by
        rw [List.getElem?_map, Hpx]; rfl
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
      have Hn1 : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by
        unfold sint.nat at Hmsll; word
      have Hpxps : px.2 ∈ ps := by
        rw [← Hmps]; exact List.mem_map.2 ⟨px, List.mem_of_getElem? Hpx, rfl⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ px.1 Hn.1 $$ [Hmsl] as Hmsl
      · iframe Hmsl; ipureintro; exact Hmx
      icases (BigSepL.bigSepL_lookup_acc_impl
          (Φ := fun _ (p : Loc × w64) => memberDirIs (GF := GF) dir p.1 p.2) Hpx)
        $$ Hmso with ⟨Hmo, Hmso⟩
      iunfold memberDirIs at Hmo
      icases Hmo with ⟨%Hmnn, %mpu, %mcu, %mil, %mnm, %mpus, %mcus, Hmid, Hmpu, Hmil, Hmnm, Hmcu, Hmpus, Hmcus, %Hmok⟩
      (try wp_auto)
      wp_if_destruct
      · ihave Hmso : iprop([∗list] p ∈ mps, memberDirIs (GF := GF) dir p.1 p.2)
            $$ [Hmso Hmid Hmpu Hmil Hmnm Hmcu Hmpus Hmcus]
        · ihave Hmso := Hmso $$ %(fun (_ : Nat) (p : Loc × w64) => memberDirIs (GF := GF) dir p.1 p.2)
          iapply Hmso
          · iintro !> %k %y %_ %_ H; iexact H
          · iunfold memberDirIs
            isplitl []
            · ipureintro; exact Hmnn
            iexists mpu, mcu, mil, mnm, mpus, mcus
            iframe; ipureintro; exact Hmok
        have Hpid : px.2 = id := by rw [← Hid]; simpa using Hif
        wp_for_post
        iframe
        iexists n + W64 1, _, L
        iframe
        ipureintro
        refine ⟨⟨by word, by word, by omega⟩, ?_⟩
        rw [Hn1]
        exact membersCov_step mps id L L _ px Hpx Hcov (fun _ h => h) (fun h => absurd Hpid h)
      · have Hpid : px.2 ≠ id := by rw [← Hid]; simpa using Hif
        obtain ⟨Hne, Hpl, Hown, Hpm⟩ :=
          addPeer_dir γn dir Hγn.2 Hdirok ps Hdirps.1 px.2 Hpxps mpus Hmok.2
        have H8 : 8 ≤ 2 ^ 23 - 8 * L.length := by
          have h1 : mps.length = (sint.Z msl.len).toNat := Hmsll.1
          have h2 := Hn.2.2
          omega
        icases replicate_takeN _ 8 _ H8 $$ HlgPeers with ⟨HR8, HlgPeers⟩
        wp_apply (h41 γn t c L px.2 mpu (DFrac.own 1) mpus Hne Hpl Hown
            (by rw [Hcl]; exact fun h => Hpid h.symm) Hpm) $$ [Htlive Hmpus HR8]
          as ⟨Htlive, Hmpus, Hnr1⟩
        · iframe Htlive Hmpus
          iframe #
          rw [HcR]
          iexact HR8
        (try wp_auto)
        ihave Hmso : iprop([∗list] p ∈ mps, memberDirIs (GF := GF) dir p.1 p.2)
            $$ [Hmso Hmid Hmpu Hmil Hmnm Hmcu Hmpus Hmcus]
        · ihave Hmso := Hmso $$ %(fun (_ : Nat) (p : Loc × w64) => memberDirIs (GF := GF) dir p.1 p.2)
          iapply Hmso
          · iintro !> %k %y %_ %_ H; iexact H
          · iunfold memberDirIs
            isplitl []
            · ipureintro; exact Hmnn
            iexists mpu, mcu, mil, mnm, mpus, mcus
            iframe; ipureintro; exact Hmok
        ihave ⟨Hun, Hnr⟩ := trNoRemAcc_snoc c L px.2 $$ Hun Hnr Hnr1
        wp_for_post
        iframe
        iexists n + W64 1, _, L ++ [px.2]
        iframe
        isplitl [HlgPeers]
        · rw [show 2 ^ 23 - 8 * (L ++ [px.2]).length = 2 ^ 23 - 8 * L.length - 8 by
            simp only [List.length_append, List.length_singleton]; omega]
          iexact HlgPeers
        ipureintro
        refine ⟨⟨by word, by word, by simp only [List.length_append, List.length_singleton]; omega⟩, ?_⟩
        rw [Hn1]
        exact membersCov_step mps id L (L ++ [px.2]) _ px Hpx Hcov
          (fun x hx => List.mem_append_left _ hx) (fun _ => List.mem_append_right _ (by simp))
    · wp_join_done
      iexists L
      iframe
      ipureintro
      exact membersCov_done γn dir Hγn.2 ps Hdirps.1 mps Hmps id L (sint.Z n).toNat
        (by have h1 : mps.length = (sint.Z msl.len).toNat := Hmsll.1; omega) Hcov
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
  have hγs : envAgree (GF := GF)
      ⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ E₀ :=
    ⟨Hγw.2.2.2.1, Hγw.2.2.2.2, rfl⟩
  -- the transport, started: (rafthttp stage 6d) frozen, every other member a peer; the network's
  -- transport, its `Send` with the raft loop's key (fixed to it now)
  -- (D22 J-T, 2026-10-27: until then frozen here, D41) the transport stays live, the apply
  -- thread's (`srvApRes`); opened now that every other member is a peer, the no-remote tokens
  -- collected (`srvTrTok`'s)
  ihave #Hst : trState γn t c $$ [Htlive]
  · iunfold trLive at Htlive; icases Htlive with ⟨#H, -⟩; iexact H
  imod (trOpen_state γn t c) $$ Hst Hun with #Hop
  have HcLnd : c.L.Nodup := by rw [HcL]; exact Hrnodup.filter _
  have HcLm : ∀ f, f ∈ c.L ↔ f ∈ ps ∧ f ≠ id := by
    intro f; rw [HcL, List.mem_filter]; simp
  have HcLcov : ∀ f ∈ c.L, f ∈ L := by
    intro f hf
    rw [HcLm] at hf
    apply Hcov f _ hf.2
    rw [netRh_member, Hγn.2]; exact (Hdirps.1 f).2 hf.1
  ihave Hnrs := trNoRemAcc_full c L HcLnd HcLcov $$ Hnr
  ihave #Htrall0 := HtrNet
  imod (srvSendKey_fix γk s t c) $$ Hk with #Hkx
  ihave #Htrall : netTransport γn id (transportIface t) (srvTrKey γn γk) iprop(False) $$ []
  · rw [← Hcl]
    iapply netTransport_noStop
    iapply (netTransport_of_key γn c.lid (transportIface t) γk s t c HcR) $$ Hkx Htrall0
  -- the transport's reader tokens: the raft loop's key, `CutPeer`'s and `MendPeer`'s, and the
  -- requests' its handler serves
  icases replicate_take1 _ _ (by omega) $$ Htoks with ⟨HtokS, Htoks⟩
  icases replicate_take1 _ _ (by omega) $$ Htoks with ⟨HtokP, Htoks⟩
  icases replicate_takeN _ http.httpProcSlots _ (by omega) $$ Htoks with ⟨HtokServe, -⟩
  ihave Hsend : srvTrKey γn γk $$ [HtokS]
  · iapply srvTrKey_of_trTok γn γk s t c HcR $$ [HtokS]
    iframe #
    iexact HtokS
  ihave HServe : ([∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn ⟨t, c⟩)
      $$ [HlgServe HtokServe]
  · unfold srvServeRes
    simp only
    rw [HcR]
    iapply replicate_sep $$ [HlgServe HtokServe]
    iframe
  -- the read names
  iunfold srvReadNamesFreshNK at Hrd
  icases Hrd with ⟨Hap, Hcm, Hnot, Hlogs, Hpend, Hkhi⟩
  icases hHalves _ _ $$ Hkhi with ⟨Hkhi1, Hkhi2⟩
  ihave ⟨Hkvw, #Hcert0⟩ := txn.kvWriter_cert kst γw.st [[], []] $$ Hkvw
  ihave #Hrlb : srvRLogLb ρ.rd.raft [] $$ []
  · iunfold srvRaftLogInv at Hrli
    icases Hrli with ⟨-, #H, -⟩
    iexact H
  -- the indices
  imod (srvIndices_allocM on s
      ⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ ρ.rd ⊤
      (by rw [HρRaft]))
    $$ [appliedIndex] [committedIndex] [term] Hap Hcm Hlogs Hpend [] Hrlb []
    with ⟨#Hai, Haown, #Hal0, #Hcmi, Hcmown, #Hti⟩
  · iapply hU64; iexact appliedIndex
  · iapply hU64; iexact committedIndex
  · iapply hU64; iexact term
  · simp only [Hlog0]; rw [Hγw.2.2.2.1]; iexact Hcert0
  · iapply appliedPubM_zero on _ ρ.rd (by rw [HρRaft]) $$ Hrlb
    iExactEq Hpub0
    rfl
  -- the KV invariants
  imod (kvCertInvM_alloc on ρ.rd.raft ρ.rd.kv srvAuthSt0 ⊤ (by rw [Hlog0]; simp)) $$ [Hcok] Hkhi1 Hrlb
    with #Hkci
  · rw [Hcok, ← Hγw.2.2.2.2]; iexact Hcok
  -- the mints
  have hργ : ρ.raft.raft = γ := by simp only [ReqNames.raft, HρRaft]
  imod (srvMintInv_alloc ρ ⊤) $$ [] [] [HrdCred] with #Hmint
  · iexact Hpmint
  · iexact Hrdctx
  · rw [hργ]; iexact HrdCred
  -- `lead`, `leadTimeMu`, `bemu`
  imod (inv_alloc srvN ⊤ iprop(∃ v : w64, sync.atomic.ownUint64 (srvLeadAddr s) (DFrac.own 1) v))
    $$ [lead] with #Hlead
  · inext; iexists W64 0; iapply hU64; iexact lead
  ihave #Hsyncpkg : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  imod sync.init_RWMutex (leadTimeP s) (E := ⊤) (srvLeadTimeMuAddr s) $$ [leadElectedTime] leadTimeMu
    with Hltslots
  · inext; iunfold leadTimeP; iexists _; iexact leadElectedTime
  icases sync.ownRWMutex_slots_guard _ _ $$ Hltslots with ⟨Hltslots, #Hltg⟩
  -- (D19g (b)) `leadTimeMu`'s reader slots for request goroutines
  icases replicate_takeN _ 64 _ (by omega) $$ Hltslots with ⟨Hlts, -⟩
  -- (D22 receiver epochs, S7b) half of `s.be` the apply thread's (`srvBeOwn`); until then (D19i
  -- part 2) kept out of `bemu` for good, the storage version monitor's
  icases (typedPointsto_dfractional (GF := GF) (srvBeAddr s) (srvBeIface d.be)).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [be] with ⟨be, beA⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact be
  imod sync.init_RWMutex (bemuP s γbe) (E := ⊤) (srvBemuAddr s) $$ [be Hγbm] bemu with Hbmslots
  · inext; iunfold bemuP; iexists d
    iframe be Hγbm
    iunfold srvBeRO; iexists batchLockInv γA (metaTM d.γB d.P); iexact HB
  icases replicate_take1 _ _ hM1 $$ Hbmslots with ⟨Hbmr, Hbmslots⟩
  -- (D19g (b)) `v3rpc.Server`'s reader slot of `bemu`
  icases replicate_take1 _ _ (by omega) $$ Hbmslots with ⟨Hbmr2, Hbmslots⟩
  -- (D22g (A)) the quota checks' reader slots of `bemu`, for request goroutines
  icases replicate_takeN _ 64 _ (by omega) $$ Hbmslots with ⟨Hbms, Hbmslots⟩
  -- (D19i part 2) the storage version monitor's
  icases replicate_take1 _ _ (by omega) $$ Hbmslots with ⟨HbmSV, -⟩
  -- the raft node, its transport installed
  ihave #Henv : rnEnvOk (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) bud id (srvTrKey γn γk)) γrn $$ []
  · iapply (rnEnvOk_of_clusterM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) bud γrn
      (by rw [Hrn1, hργ]) (by rw [Hrn6]; simp only [ReqNames.raft, HρRaft])
      (by rw [Hrn6]; simp [ReqNames.raft, HρRaft]) (by simp only [ReqNames.raft, HρRaft])
      ⟨fun _ => by rw [Hrn1]; exact Hrn4d.1 rfl, fun _ => Hrn4⟩ (fun dec c0 h0 h1 h => by rw [Hrn4] at h; cases h)
      (by rw [Hrn3, Hrn7]) Hrn2
      (by first | (rw [← hργ]; exact Hnosnap.1) | (rw [hργ]; exact Hnosnap.1) | exact Hnosnap.1)
      (by rw [Hrn8, Hnosnap.2]; exact Int.le_refl _) id (srvTrKey γn γk)
      (by rw [Hrn5n, Hrid]))
    iframe Hkvinv Hrli
    iapply clusterWorkloadOkM_of on ρ E₀
    iframe Hkvinv Hrli HNZ0
  imod Hinst $$ %(srvRAddr s) %s %(interface.mkOk (go.GoType.PointerType api.rafthttp.Transport.ty) #t)
    [Henv] [Hcmi] [] [Htrf] [HlatestTs] [] [Hrtm] with ⟨#Hrn, Hrdone, #Hnodef, #Hprop, #Htrf⟩
  · iexact Henv
  · iexact Hcmi
  · iexact Hfix
  · iexact Htrf
  · iexact HlatestTs
  · -- (D21 M2) the raft wrapper's messages carry their bundle into the network
    ihave #Htrall' : netTransport γn id (transportIface t)
        (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) bud id (srvTrKey γn γk)).S
        (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) bud id (srvTrKey γn γk)).ST $$ []
    · rw [show (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) bud id (srvTrKey γn γk)).S = srvTrKey γn γk
        from rfl,
        show (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) bud id (srvTrKey γn γk)).ST = iprop(False)
        from rfl]
      iexact Htrall
    iapply isRNTransport_of_net γn id $$ [] Htrall'
    iintro !> %m HM
    simp only [srvErM]
    rw [Hγn.1, ← hργ]
    iapply (srvMsgNet_bundle _ bud id m
      (by first | (rw [← hργ]; exact Hnoxfer) | (rw [hργ]; exact Hnoxfer) | exact Hnoxfer)) $$ HM
  · iexact Hrtm
  -- (D17d) `run`'s snapshot contract, from the storage's snapshot token
  ihave Hgap : srvBuildGap s γrn (W64 0) (W64 0) $$ [Htok]
  · iunfold srvBuildGap
    rw [Hrn8]
    iapply rnSnapOnce_of_tok h85 _ γrn (srvRAddr s) bv.storage' γs Hrn7 $$ Hpkg Hrn Htok
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  iNamedPrefix Hrn' "N"
  -- the lessor
  ihave #Hlok : lessorOk (lease.lessorIface lp) $$ []
  · iapply lessorOk_of_lessorInv h57 h58 h59 lp γl
    iframe Hlexp Hlcfg Hlinv Hlspkg
  ihave #Hapl : apply.isApplyLessor (lease.lessorIface lp) kst γw.st
      (batchLockInv γA (metaTM d.γB d.P)) #hook (srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be)) $$ []
  · iapply apply.isApplyLessor_of_lessorInv h49 h50 h51 h52 h53 h54 h55 h56 lp kst γw.st _ _ _
      (lease.lessorBeOn lp d.be) (backend.rbOwn d.γB)
    rw [Hγw.2.1]
    iframe Hllk Hlcfg Hlinv Hlspkg
    isplitl []
    · unfold mvcc.storeWT mvcc.storeRT
      rw [Hγw.2.2.1, show mvcc.kbWT (GF := GF) (some d) = backend.wbTok d.γB from rfl,
        show mvcc.kbRT (GF := GF) (some d) = mvcc.bkRTx d.γB d.P d.be from rfl]
      iunfold lessorApplyOk at Hlbe
      iapply Hlbe $$ %d %(mvcc.lateW d.gx) %(batchLockInv γA (metaTM d.γB d.P)) %hook
        %(lease.lessorBeOn lp d.be) HB Hhook [] []
      · ipureintro; exact Hhknn
      · iapply lessorBeOn_lens
    · iapply srvRestRWH_lessor
  ihave #Hast : apply.isAuthStore ast γw.st (batchLockInv γA (metaTM d.γB d.P)) #hook RD M
      (srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be)) $$ []
  · rw [Hastl]
    iunfold authApplyOkM at HisAuth
    iapply HisAuth $$ %d %(mvcc.lateW d.gx) %(batchLockInv γA (metaTM d.γB d.P)) %γw.st %hook
      %(srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be)) [] HB Hhook [] []
    · ipureintro; exact Hγw.2.2.1
    · ipureintro; exact Hhknn
    · iunfold rwLens
      iintro !> Hrw
      iunfold srvRestRWH at Hrw
      iunfold srvObjsOn at Hrw
      icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
      isplitl [Hrw Hau]
      · iframe Hrw Hau
      iintro ⟨Hrw, Hau⟩
      iunfold srvRestRWH
      iunfold srvObjsOn
      iframe Hrw Hal Hau Hle Hcb
  -- the persistent fields
  ipersist reqIDGen
  ipersist firstCommitInTerm
  ipersist errorc
  ipersist compactor
  ipersist MaxRequestBytesS
  ipersist ClientCertAuthEnabledS
  -- (D22 S-h) `s.inflightSnapshots`'s invariant, from the field's zero value
  ihave Hinfl0 : sync.atomic.ownInt64 (GF := GF) (srvInflightAddr s) (DFrac.own 1) (W64 0)
    $$ [inflightSnapshots]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact inflightSnapshots
  imod inv_alloc srvInflightN ⊤
    iprop(∃ n : w64, sync.atomic.ownInt64 (GF := GF) (srvInflightAddr s) (DFrac.own 1) n)
    $$ [Hinfl0] with #HinflI
  · inext; iexists _; iexact Hinfl0
  ihave #Hinfl : srvInflight s $$ []
  · iunfold srvInflight; iexact HinflI
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨Hlr5, Hlgrs⟩
  icases replicate_take1 _ _ hM1 $$ Hfcnr with ⟨Hfcr, -⟩
  -- the watch-token pool (D19b's method), from `mvcc.New`'s tokens
  imod (mvcc.watchTokPool_alloc γw ⊤ (by omega)) $$ Hwtoks with #Hpool
  -- (D19g (b)) what serving needs: the configuration fields, the watchable store as the KV, the
  -- progress interval's field, `lgMu`'s reader slots for request goroutines and the others'
  icases replicate_takeN _ 64 _ (by omega) $$ Hlgrs with ⟨Hlgs, Hlgrs⟩
  -- (D19i part 2) the storage version monitor's `lgMu` reader slot
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨HlgSV, Hlgrs⟩
  -- (audit B4a) `monitorDowngrade`'s `lgMu` reader slot, and the monitors' configuration fields
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨HlgMon, Hlgstock⟩
  ipersist CorruptCheckTimeS
  ipersist DowngradeCheckTimeS
  ihave HMon : srvMonitorCfg s cfg $$ [HlgMon]
  · iunfold srvMonitorCfg; rw [Hfgi]; iframe DowngradeCheckTimeS CorruptCheckTimeS ServerFeatureGateS; iframe HlgMon
  ipersist LoggerS
  ipersist MaxTxnOpsS
  ipersist WarningUnaryRequestDurationS
  ipersist MetricsS
  ipersist EnableDistributedTracingS
  ipersist TracerOptionsS
  ipersist MaxConcurrentStreamsS
  -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`srvSnapBoot`,
  -- `SnapRO.lean`): its persistent bundle, the snapshot-taken counter's authority, the stocks of
  -- the auth store's reader resource and `lgMu`'s reader slots (dropped here until J1a)
  ipersist DataDirS
  ipersist snapshotter
  ipersist beHooks
  have hMR3 : 2 ^ 29 + 2 ^ 28 + 2 ^ 23 + 2 ^ 22 + 200 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  obtain ⟨stp, Hstp, Hstpss⟩ := Hrn15
  ihave HsnapB : srvSnapBoot s cil
      (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ : apply.AEnv GF)
      ρ.rd $$ [Hγt HRDstock Hlgstock]
  · iunfold srvSnapBoot
    iexists γt
    iframe Hγt
    isplitr [HRDstock Hlgstock]
    · icases Hbh with ⟨%lgh, #Hbh'⟩
      ihave #Hfix' := Hfix
      iunfold rnFixed at Hfix'
      iNamed Hfix'
      iunfold srvSnapRO
      imodintro
      iexists cfg, bs.ss', bk.beHooks', lgh, stp, γd, bc.nodeID', alst, astl, lp, bc.cl', ps, dir, d
      simp only
      rw [← Hstp, ← Hastl, Hfgi]
      iframe LoggerS DataDirS ServerFeatureGateS Hfg QuotaBackendBytesS WarningApplyDurationS
      iframe snapshotter Hss beHooks Hbh' storageC memberID alarmStore authStore lessor cluster
      iframe HalS HalA HisAuth HauR Hlbe Hlcfg Hrc Hisc Hsz
      isplitr
      · ipureintro
        refine ⟨Hγw.2.2.1, Hlgnn, Hstpss, Hdbo, Hbuq, ?_, Hdirps.1⟩
        rw [HρRaft, Hid]; exact Hsloc
      isplitr
      · iExactEq Hsdir
        rw [Hγn.1, HρRaft]; rfl
      isplitr
      · iunfold lessorLookupOk; iexact Hllk
      isplitr
      · iexists _; iexact Hvcn
      iunfold srvMembersDir; iexact Hmembers
    · iunfold srvSnapStock
      iexists _, _
      iframe HRDstock Hlgstock
      ipureintro; constructor <;> omega
  -- (S7b) the request path's `bemu` reader slots, at some current backend's ghost variable
  ihave Hbmr2 : srvBemuReader (GF := GF) s $$ [Hbmr2]
  · iunfold srvBemuReader; iexists γbe; iunfold srvBemuReaderAt; iexact Hbmr2
  ihave Hbms := replicate_mono _ (srvBemuReader (GF := GF) s) 64
    (by iintro H; iunfold srvBemuReader; iexists γbe; iunfold srvBemuReaderAt; iexact H) $$ Hbms
  ihave Hserve : srvServeBuilt s
      (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ : apply.AEnv GF)
      cfg 64 $$ [WatchProgressNotifyIntervalS Hbmr2 Hlts Hlgs HRDs Hsrs Hbms]
  · unfold srvServeBuilt srvServeFacts srvServeCfg srvLeadTimeReader
    isplitr
    · isplitr
      · iexists ws, γw
        iframe kv Hws
        ipureintro; rfl
      · iframe MaxConcurrentStreamsS TracerOptionsS EnableDistributedTracingS MetricsS WarningUnaryRequestDurationS MaxTxnOpsS LoggerS QuotaBackendBytesS
    iframe WatchProgressNotifyIntervalS Hbmr2 Hlts Hlgs HRDs Hsrs Hbms
  -- (D19i part 2) the storage version monitor's read token, with an open share
  -- (D19i part 2) the storage version monitor's backend access
  ihave HSV : srvSVRes s
      (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ : apply.AEnv GF)
      $$ [HbmSV HlgSV]
  · unfold srvSVRes srvBemuReaderAt
    iframe HbmSV HlgSV
  -- (D21 M5) the server is member `id` of the network: `RaftHandler`'s premise
  ihave #Hnm : srvNetMember γn s id ⟨t, c⟩ $$ []
  · iunfold srvNetMember
    iframe Hprocok
    simp only
    iframe Htrf
    isplitr
    · ipureintro; exact Hcl
    iframe Hst Hop
    ipureintro
    intro f hf hne
    rw [HcLm]
    refine ⟨?_, hne⟩
    rw [netRh_member, Hγn.2] at hf
    exact (Hdirps.1 f).1 hf
  ihave HtokP : srvTrTok γn ⟨t, c⟩ $$ [HtokP Hnrs]
  · iunfold srvTrTok; iframe
  -- (2026-10-23) `readych`, as a broadcast channel not yet closed: `publishV3`'s to close
  ipersist readych
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γrdc rdc $$ Hrdc Hrdo with Hrdb
  ihave Hrc : srvReadyCloser s $$ [Hrdb]
  · unfold srvReadyCloser
    iexists rdc, γrdc
    iframe readych
    iframe Hrdb
  -- (2026-10-20, watchkv) the watchable store's reader slots for the watch service
  ihave HWR : srvWatchReaders s
      (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ : apply.AEnv GF)
      64 $$ [Hwrx]
  · unfold srvWatchReaders
    iexists ws, γw
    simp only
    iframe Hpool kv Hws Htag
    iframe Hwrx
  -- (the auth plan's E2k) the auth store's resources for the apply thread
  ihave HAR : srvAuthApplyResB s
      (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ : apply.AEnv GF) srvAuthSt0 $$ [HAres]
  · unfold srvAuthApplyResB
    iexists astl, d.be
    rw [← Hastl]
    iframe authStore
    isplitl [HAres]
    · -- (E3n) the construction's resource at the server's frozen hook
      iapply (authApplyResB_of_pre M astl srvAuthSt0 d (mvcc.lateW d.gx)
        (batchLockInv γA (metaTM d.γB d.P)) hook)
      iframe HB Hhook
      isplitl [HAres]
      · iExactEq HAres
        rfl
      ipureintro; exact Hhknn
    -- (E3l) the equation of the backend names: the write right lends the store's half on `d.be`
    isplitr
    · iapply rwLens_authBeOn
    -- (E3n) and so does the rest resource, at the same rest value
    iapply roLends_authBeOn
  imodintro
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexists γA, cil, metaTM d.γB d.P,
    (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ : apply.AEnv GF),
    γrn, (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be : GoInterface), γk,
    (⟨t, c⟩ : SrvTr GF)
  iframe Hgap Hserve HSV HMon Hrc Hnm HWR HtokP HServe
  isplitr
  · icases HM with %HM; ipureintro; exact ⟨hγs, HM⟩
  isplitr
  · unfold srvWatchBuilt
    iexists ws, γw
    simp only
    iframe Hpool kv Hws Htag
  isplitl [Hwcl]
  · -- (D22 S-g) the KV's closer, kept (until then dropped here)
    unfold srvKVCloser
    iexists ws
    iframe kv
    iexact Hwcl
  -- (D22 S-j2) the backend file's directory entry, `bootOk`'s, kept
  iframe Hpath
  unfold srvBuiltG
  iframe HsCI Hloop Happly Hrdone Hcci Hwci Hai Hti Hcmi Hrn
  isplitr
  · -- `#Hfb`
    iexists ⟨cfg.Logger', GoInterface.nil, lease.lessorIface lp, #hook, fcn, alst, bc.cl',
      cfg.QuotaBackendBytes', «$v2_ptr», bc.nodeID', cfg.ElectionTicks', cfg.TickMs'⟩
    unfold srvFieldsBuiltNA srvLeadInv
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro; exact ⟨⟨rfl, rfl⟩, rfl, rfl, d.γB, _, rfl, rfl, d, alst, astl, lp, Hγw.2.2.1, rfl, rfl⟩
  isplitr
  · -- `#Hreqb`
    iexists ⟨gen, GoInterface.nil, cfg.MaxRequestBytes', cfg.ServerFeatureGate',
      cfg.ClientCertAuthEnabled', cfg.ElectionTicks', cfg.TickMs', ast, null, bc.nodeID', bc.cl',
      interface.mkOk (go.GoType.PointerType api.rafthttp.Transport.ty) #t, cid⟩
    unfold srvReqBuiltM srvAtomicU64 srvPeersOk
    dsimp only
    rw [Hfgi]
    iframe ClientCertAuthEnabledS MaxRequestBytesS reqIDGen Htrf Hlead Hmint Htrr memberID cluster authStore HisReq ServerFeatureGateS TickMsS ElectionTicksS Hcid Hrc Hkvinv Hfg
    isplitr
    · have hff : srvFloorFact (GF := GF)
          ⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ =
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
    iframe firstCommitInTerm Hast Hapl Hti Hcert0 WarningApplyDurationS lessor authStore lg
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro; simp
  isplitr
  · -- `#Hrunb`
    iexists ⟨errc, null, null, func.nil, GoInterface.nil, sstats, null⟩
    unfold srvRunBuilt compactorOk
    iframe compactor errorc Hltg stats Herrb
    ileft; ipureintro; rfl
  isplitr
  · -- `#Hsab`: (D19p) `msgSnapC` never delivers
    unfold srvApplyAllBuilt
    iexists _
    iframe NHmsc
    iunfold isRNMsgSnapC at NHmsci
    icases NHmsci with ⟨%γmc, #Hmcb⟩
    iframe Hinfl
    iexists γmc, _
    iframe Hmcb
    iintro !> %mm Hmm
    iapply rnSnapMsg_false γrn.node (by rw [Hrn1]; exact Hnosnap.1) mm $$ Hmm
  isplitr
  · -- `#Hkvi`
    unfold srvKVInvsM Perennial.named
    iframe Hkci Hrli Hkvinv
    ipureintro; exact (Hγw.2.2.2.2.trans Hcok.symm)
  isplitr
  · ipureintro
    refine ⟨?_, rfl, fun _ => Int.le_refl _⟩
    unfold srvErM
    simp only
    exact (srvCM_agree on ρ _ E₀ (W64 0) (W64 0) (bootKVOf on) hγs).symm
  isplitr
  · ipureintro; rfl
  isplitl [Hsend]
  · simp only [srvErM]; iexact Hsend
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
  · iexists _; iframe SnapshotCatchUpEntriesS; ipureintro; exact HrbS
  isplitl [wg]
  · iexact wg
  isplitl [wgMu]
  · iexact wgMu
  isplitl [Hcmown]
  · iexists _; iexact Hcmown
  isplitl [Hnot]
  · iexact Hnot
  isplitl [Hthr Happ Hown Hlr5 Hbmr beA HγbA Hrev HAR Haown Hkhi2 forceDiskSnapshot Hrbo Hmem HalOn HauthOn HleOn HclBe Htlive]
  · -- `Happ` (E3c: the mode-`on` row, the auth resource at the store's start state)
    iapply applyBuiltNAM_of_On
    unfold applyBuiltNAOn srvBemuReaderAt
    iexists ⟨W64 0, W64 0, W64 0, false⟩, W64 0, W64 0, false
    iframe Hthr Happ Hlr5 Hbmr Haown forceDiskSnapshot
    isplitr
    · ipureintro
      have hm0 := Hci.2
      refine ⟨⟨rfl, ?_⟩, ?_⟩ <;> simp [ciEff, hm0]
    isplitl [Hown]
    · unfold applyBackend
      iframe Hown Hmeta
    isplitl [beA HγbA]
    · iunfold srvBeOwn; iexists d; iframe beA HγbA; ipureintro; exact Hγw.2.2.1
    isplitl [Hrev]
    · unfold revAuth
      iexists ∅
      iframe Hrev
      ipureintro; intro k hk; simp at hk
    isplitl [HAR]
    · iexact HAR
    isplitr
    · simp only [bootKVOf]; rw [← Hlog0]; iexact Hal0
    isplitr [Hrbo Hmem HalOn HauthOn HleOn HclBe Htlive]
    · unfold kvRun kvApplied kvAppliedL kvCert
      iframe Hrlb
      isplitl [Hkhi2]
      · isplitl [Hkhi2]
        · isplitl [Hkhi2]
          · first
              | iexact Hkhi2
              | (simp only [bootKVOf]; rw [← Hlog0]; iexact Hkhi2)
          isplitr
          · ileft; ipureintro; simp [Hlog0, bootKVOf]
          ipureintro; simp [kvModel, kvRaftOf_nil, Hlog0, bootKVOf]
        ipureintro; simp [bootKVOf, Hch0]
      ipureintro; exact ⟨Hc0, by simp [ReqNames.raft, HρRaft]⟩
    · -- (D22, 2026-10-23) the rest buckets and the members at the start: the boot state
      unfold srvRest
      have hpre : ρ.rd.raft.pre = [] := by simp [HρRaft]
      have hboot : ρ.rd.raft.raft.reBoot = bootLog := by rw [HρRaft]; exact Hrboot
      rw [hpre, hboot, List.append_nil, restModel_nil]
      dsimp only
      isplitl [Hrbo Hmem HalOn HauthOn HleOn HclBe]
      · unfold srvRestOwnH srvRestOwn restBoot srvObjsOn
        iframe Hrbo Hmem HalOn HauthOn HleOn HclBe
      -- (D43 M5e) the apply thread's membership resource: the frozen transport's stop token
      have hdn : γ.reDyn = none := Hrn4d.mp rfl
      have hργ : ρ.rd.raft.raft = γ := by rw [HρRaft]
      iunfold srvApRes
      icases Hbh with ⟨%lgh, #Hbhi⟩
      icases Hclg with ⟨%lgc, #Hclgf, %Hlgcnn⟩
      iunfold membership.clusterCid at Hcid
      iexists bk.beHooks',
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩,
        lgh, t, id, bc.cl', lgc, cid, L
      rw [← Hid]
      iframe beHooks Hbhi Htrf memberID cluster Hclgf Hcid
      isplitr
      · ipureintro; exact Hlgcnn
      unfold ccMembRes srvDynLog
      rw [hργ, hdn]
      dsimp only
      iframe Hrc
      isplitl [Htlive]
      · iexists γn, c
        iframe Htlive
        ipureintro; rw [Hcl, Hid]
      ipureintro
      refine ⟨⟨fun _ f hf hne => ?_, ?_⟩, trivial⟩
      · apply Hcov f _ (by rw [Hid] at hne; exact hne)
        rw [netRh_member, Hγn.2]
        rw [hργ, Hrcfg, GMap.elem_of_list_to_set] at hf
        exact (Hdirps.1 f).2 hf
      · exact srvMemOk_boot _ _ γ.reCCOk ps (by rw [HρRaft]) (by rw [hργ]; exact Hrcfg) Hrnodup
          Hrpslen (by rw [hργ, Hrboot]; exact Hrbok)
  iframe Hlr3 Hlr4
  isplitl [Hfcr]
  · iexists fcn
    iframe firstCommitInTerm Hfcr
  isplitr
  · -- `#Hkv`: the watchable store and its store's read view (`mvcc.New`)
    iexists _, rv
    iframe #
  -- `HWB`: the stores' write budget
  isplitl [Hwts HγbW HrtSV]
  · iunfold srvWTStock; iexists d
    isplitr
    · ipureintro; exact Hγw.2.2.1
    iframe Hwts HγbW
    ihave HrtSV : mvcc.kbRT (GF := GF) (some d) $$ [HrtSV]
    · rw [← Hγw.2.2.1]; iexact HrtSV
    unfold mvcc.bkRTx
    iunfold mvcc.kbRT at HrtSV
    iexact HrtSV
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
    · iframe Hcvm Hpkg cluster; iframe Hk
    inext; iintro %v Hv; iapply HΦ' $$ Hv
  isplitr
  · ipureintro; exact Hbnd
  -- `Hua`: the uber-applier (D14i): its options' contracts, its chain, the apply thread's KV
  have hm0 : γA.m0.1 = W64 0 := by rw [Hci.2]
  have hLoaded : ∀ st : ApplyState, stLoaded γA st = st := by
    intro st; unfold stLoaded; split
    · rename_i h; cases st; simp only at h; subst h; simp [hm0]
    · rfl
  ihave #Hbo : apply.backendOptsOk (⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ : apply.AEnv GF) uopts $$ []
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
    · iapply (mvcc.hookOk_of_init γw.st _ #func.nil d Hγw.2.2.1 hook Hhknn)
      iframe Hhook HhkI
    isplitr
    · iexact Hapl
    isplitr
    · iexact Hast
    isplitr
    · iunfold alarmApplyOk at HalA
      iapply HalA $$ %d %(mvcc.lateW d.gx) %(batchLockInv γA (metaTM d.γB d.P)) %γw.st %hook
        %(srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be)) [] HB Hhook [] []
      · ipureintro; exact Hγw.2.2.1
      · ipureintro; exact Hhknn
      · iunfold rwLens
        iintro !> Hrw
        iunfold srvRestRWH at Hrw
        iunfold srvObjsOn at Hrw
        icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
        isplitl [Hrw Hal]
        · iframe Hrw Hal
        iintro ⟨Hrw, Hal⟩
        iunfold srvRestRWH
        iunfold srvObjsOn
        iframe Hrw Hal Hau Hle Hcb
    isplitr
    · iunfold clusterApplyOk at Hisc
      iapply Hisc $$ %d %(mvcc.lateW d.gx) %(batchLockInv γA (metaTM d.γB d.P)) %γw.st %hook
        %(srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be))
        %(srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be)) [] HB Hhook [] [] [] []
      · ipureintro; exact Hγw.2.2.1
      · ipureintro; exact Hhknn
      · iexists _; iexact Hvcn
      · iunfold roLens
        iintro !> %r Hro
        iunfold srvRestOwnH at Hro
        iunfold srvObjsOn at Hro
        icases Hro with ⟨Hro, Hal, Hau, Hle, Hcb⟩
        dsimp only
        isplitl [Hro Hcb]
        · iframe Hro Hcb
        iintro %r' ⟨Hro, Hcb⟩
        iunfold srvRestOwnH
        iunfold srvObjsOn
        iframe Hro Hal Hau Hle Hcb
      · iunfold rwLens
        iintro !> Hrw
        iunfold srvRestRWH at Hrw
        iunfold srvObjsOn at Hrw
        icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
        isplitl [Hrw Hcb]
        · iframe Hrw Hcb
        iintro ⟨Hrw, Hcb⟩
        iunfold srvRestRWH
        iunfold srvObjsOn
        iframe Hrw Hal Hau Hle Hcb
    isplitr
    · iunfold apply.isRaftStatus
      iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
      isplitr
      · ipureintro; rfl
      isplitr
      · iintro !> !> %Φ' - HΦ'
        iapply (h79 s bc.nodeID') $$ [] [HΦ']
        · iframe Hpkg memberID
        inext; iintro -; iapply HΦ'; itrivial
      isplitr
      · iintro !> !> %Φ' - HΦ'
        iapply (h80 s) $$ [] [HΦ']
        · iframe Hpkg
          iunfold srvLeadInv; iexact Hlead
        inext; iintro %l -; iapply HΦ'; itrivial
      · iintro !> !> %Φ' - HΦ'
        iapply (h81 s) $$ [] [HΦ']
        · iframe Hti Hpkg
        inext; iintro %t' -; iapply HΦ'; itrivial
    isplitr
    · iunfold apply.isSnapshotServer
      iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
      isplitr
      · ipureintro; rfl
      iintro !> !> %Φ' Hfs HΦ'
      iapply (h82 s) $$ [Hfs] [HΦ']
      · iframe Hpkg; iframe Hfs
      inext; iintro Hfs; iapply HΦ'; iexact Hfs
    · iunfold apply.isConsistentIndexer
      rw [Hci.1]
      iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩
      isplitr
      · ipureintro; rfl
      iintro !> %C %HC
      obtain ⟨cst, cb, hC, hcp, -⟩ := HC
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
        · iframe Hcipkg Hcons HisCI; iframe Hcst Hcb
        iintro ⟨Hcst, Hcb⟩
        rw [hLoaded]
        iframe Hcst Hcb
        ipureintro; rfl
      · iintro %w ⟨HΦ', %Hw, HP⟩
        subst Hw
        iapply HΦ' $$ HP
  ihave Hul := Hulate $$ %(⟨kst, γw.st, batchLockInv γA (metaTM d.γB d.P), #hook, RD, E₀.γrev, M, srvFS s, srvCiC γA cil, srvRestOwnH d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe⟩ : apply.AEnv GF) [] Hbo
  · ipureintro; rfl
  icases Hul with ⟨#Hui, %ns, %cr, %Hz, Huo⟩
  obtain ⟨hns, hcr⟩ := Hz trivial
  subst hns hcr
  icases replicate_take1 _ _ (by omega) $$ Hwrds with ⟨Hwrd, -⟩
  iunfold mvcc.watchReader at Hwrd
  icases Hwrd with ⟨Hsrd, -⟩
  isplitr [Hwtok HsnapB]
  rotate_left
  · iframe Hwtok HsnapB
  iapply srvUberRowM_of_On
  iexists ua
  iframe uberApply
  isplitr
  · -- (E3k) the base applier's auth layer, at the server's store and lessor
    iunfold srvUberBase
    iexists _, _
    iframe authStore lessor
    iunfold apply.uberBaseAuth
    isplitr
    · iexists up, uopts
      iframe Hui
      ipureintro; exact ⟨Hua, Huopts.2.2.2.1, Huopts.2.2.2.2.1⟩
    -- (E3s) the range check at a reader's lower bound, from the construction
    isplitr
    · iexact HstLb
    -- (E3l) the store's checks at the latest state, from the construction
    iexists astl
    isplitr
    · ipureintro; exact Hastl
    -- (E3t) publication, from the construction
    isplitr
    · iexact HstPub
    iexact HstL
  isplitr
  · iunfold apply.applierFor
    iexists up, uopts
    iframe Hui
    ipureintro; exact Hua
  iunfold apply.applyKV
  simp only [bootKVOf]
  iexists up
  isplitr
  · ipureintro; exact Hua
  isplitl [Huo]
  -- (the chain's auth layer is the environment's mode: by `HM`, not by unfolding)
  · icases HM with %HM'
    iExactEq Huo
    simp only [apply.AEnv.authOn, HM']
  iunfold apply.kvOwn
  ihave HwoA : mvcc.writerOwn γw.st $$ [HrtA HtrA]
  · iunfold mvcc.writerOwn; iframe HrtA HtrA
  iframe Hsrd Hkvw HRD2 HwoA
  iunfold apply.leasesLive
  iexists []
  isplitr
  · iunfold txn.leasesKnown; simp [mvcc.stateAfter, txn.leasesOk]
    iintro !> %l %h
    obtain ⟨a, ha, -⟩ := h
    simp [mvcc.applyChanges] at ha
  iunfold lease.lessorUser
  rw [Hγw.2.1]
  iframe Hlrd2 Hlrvk
  -- the initial state has no key: its item map is the lessor's, empty
  have h0 : (∅ : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) =
      mvcc.leaseItemsOf (mvcc.stateAfter ([[], []] : mvcc.Log)) := GMap.ext fun _ => rfl
  iapply (lease.leaseOwn_eq h0) $$ Hlown

-- (2026-10-22) the unused-variables linter walks the proof's info tree: 30s of this module's
-- CPU (on the build's critical path)
set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option pp.maxSteps 200000 in
set_option maxHeartbeats 0 in
theorem NewServer.wp_proof
    -- `int64(f)`'s semantics (`FloatToInt.lean`: a hypothesis on the semantics, as `go.Semantics`)
    [Float64ToInt64Semantics]
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
    (h84 : EtcdServer.ClusterVersion.spec (GF := GF) (hG := hG))
    (h85 : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (h86 : node.ApplyConfChange.spec (GF := GF) (hG := hG))
    -- (D21 M2) the inbound path: raft's `Step` and reports, the server's `Process` and co.
    (h87 : node.Step.spec (GF := GF) (hG := hG))
    (h88 : node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h89 : node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (h90 : EtcdServer.Process.spec (GF := GF) (hG := hG))
    (h91 : EtcdServer.IsIDRemoved.spec (GF := GF) (hG := hG))
    (h92 : EtcdServer.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h93 : EtcdServer.ReportSnapshot.spec (GF := GF) (hG := hG))
    (h94 : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG)) :
    NewServer.spec (GF := GF) (hG := hG) := by
  have h := NewServer.wp_proofM false h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    h17 h18 h19 h20 h21 h22 h23 h24 (authSrvTP_off h25 h30) h26 h27 h28 h29 h31 h32 h33 h34 h35 h36
    h37 h38 h39 h41 h42 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63
    h64 h65 h66 h67 h68 h69 h70 h71 h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83 h84 h85 h86
    h87 h88 h89 h90 h91 h92 h93 h94
  intro cfg U γ bud id bootLog ρ E₀ N Φs γn dir γd HρRaft Hpol Hc0 Hch0 Hlog0 Hcok Hlgnn Hcbl Hacr
    Hbnd Hrb HrbN HrbS Hboot Hpfx HΦs Hfgp Hdirok HpU
  -- the mode off's post (the apply thread's auth resource, `True` in the mode off, is in
  -- `srvBuilt`'s `applyBuiltNA` since E2m)
  have h' := h cfg U γ bud id bootLog ρ E₀ N Φs γn dir γd HρRaft Hpol Hc0 Hch0 Hlog0 Hcok Hlgnn
    Hcbl Hacr Hbnd Hrb HrbN HrbS Hboot Hpfx HΦs Hfgp Hdirok HpU (fun h => absurd h (by decide))
  rw [bootKVOf_false] at h'
  -- (the auth plan's E2w) the mode-indexed rows at `false` are today's
  simp only [kvInvM_false, srvErM_false, srvBuiltG_false] at h'
  iintro %Φ Hpre HΦ
  iapply h' $$ Hpre
  iintro !> %srv %err Hpost
  iapply HΦ
  icases Hpost with (Hl | ⟨%He, %γA, %ci, %TM, %E, %γrn, %b, %γk, %τ, %H1, H2, H3, H4, H5, H6, H7,
    H8, H9, H10, H11, H12, H13, H14⟩)
  · ileft; iexact Hl
  iright
  isplitr
  · ipureintro; exact He
  iexists γA, ci, TM, E, γrn, b, γk, τ
  isplitr
  · ipureintro; exact H1
  iframe H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14

end proof

end EtcdGrove
end Perennial
