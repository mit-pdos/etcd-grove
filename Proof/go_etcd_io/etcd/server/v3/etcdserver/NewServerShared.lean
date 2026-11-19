/-
The declarations `NewServer.lean` and `NewServerR.lean` share (moved out of `NewServer.lean`,
2026-11-19, proof-perf): so that the restart's proof does not import the first start's, and the two
compile in parallel (they were two thirds of the full build's longest import chain, 3m each).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestMemId
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AlarmGet
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
public import Proof.go_etcd_io.etcd.server.v3.lease.RdPool
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedServer__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewAuthBackend
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__ReadIndex
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Spec.go_etcd_io.raft.v3.node__Stop
public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
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
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke
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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Term
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ForceSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ClusterVersion
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CompactEnv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.UberKit
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopCensus
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyOptsLemmas
public import Proof.ReceiptTactics
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeStartLinked

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
instance bemuP_fractional (s : Loc) (γbe : GName) : Fractional (bemuP (GF := GF) s γbe) where
  fractional p q := by
    -- (R6, 2026-11-07) the ghost variable records the backend's key `bkKey d`, so two parts'
    -- witnesses agree on `d.be` (all the points-to reads), and the first's is kept
    have hpt : ∀ (be : Loc) (r1 r2 : Qp),
        (srvBeAddr s ↦{DFrac.own (r1 + r2).half} srvBeIface be : IProp GF) ⊣⊢
          srvBeAddr s ↦{DFrac.own r1.half} srvBeIface be ∗
            srvBeAddr s ↦{DFrac.own r2.half} srvBeIface be := fun be r1 r2 => by
      rw [show (r1 + r2).half = r1.half + r2.half from Subtype.ext (by grind)]
      exact (fractional_of_dfractional
        (fun dq => typedPointsto (GF := GF) (srvBeAddr s) (srvBeIface be) dq)).fractional
          r1.half r2.half
    have hgv : ∀ (k : backend.BNames × Loc) (r1 r2 : Qp),
        (dghostVar γbe (DFrac.own (r1 + r2).half) k : IProp GF) ⊣⊢
          dghostVar γbe (DFrac.own r1.half) k ∗ dghostVar γbe (DFrac.own r2.half) k :=
      fun k r1 r2 => by
        rw [show (r1 + r2).half = r1.half + r2.half from Subtype.ext (by grind)]
        exact (dghostVar_fractional (GF := GF) γbe k).fractional r1.half r2.half
    unfold bemuP
    constructor
    · iintro ⟨%d, Hp, Hg, #Hro⟩
      icases (hpt d.be p q).1 $$ Hp with ⟨Hp1, Hp2⟩
      icases (hgv (bkKey d) p q).1 $$ Hg with ⟨Hg1, Hg2⟩
      isplitl [Hp1 Hg1]
      · iexists d; iframe Hp1 Hg1 Hro
      · iexists d; iframe Hp2 Hg2 Hro
    · iintro ⟨⟨%d, Hp1, Hg1, #Hro⟩, ⟨%d', Hp2, Hg2, -⟩⟩
      ihave %Hk := dghostVar_agree γbe (bkKey d) _ (bkKey d') _ $$ Hg1 Hg2
      have hbe : d'.be = d.be := (congrArg Prod.snd Hk).symm
      rw [← Hk] at *
      rw [hbe]
      iexists d
      iframe Hro
      isplitl [Hp1 Hp2]
      · iapply (hpt d.be p q).2; iframe Hp1 Hp2
      · iapply (hgv (bkKey d) p q).2; iframe Hg1 Hg2

/-- **The auth history's tie to the log, allocated** (H5): the auth store's cap at its two boot
states, and the log's empty lower bound, give the tie at the empty log (`srvHist []`). -/
theorem authHistTie_alloc (E : apply.AEnv GF) (γr : ReadNames) (stl : Loc) (Eu : CoPset) :
    ⊢ authCapM E.authMode stl -∗ srvRLogLb γr.raft [] ={Eu}=∗ authHistTie E γr srvAuthSt0 := by
  unfold authCapM authHistTie
  generalize E.authMode = M
  cases M with
  | on γa =>
    iintro ⟨Hcap, %R, #Hinv⟩ #Hlb
    imod inv_alloc authTieN Eu (iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗
      auth.capAuth γa (auth.bootState :: admStates γr.kv srvAuthSt0 A))) $$ [Hcap] with #Ht
    · inext; iexists []; iframe Hlb; rw [admStates_nil]; simp only [srvAuthSt0]; iexact Hcap
    imodintro
    isplitl []
    · iexists stl, R; iexact Hinv
    iexact Ht
  | _ => iintro - -; imodintro; itrivial

end proof

end EtcdGrove
end Perennial
