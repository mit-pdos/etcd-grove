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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.FloatToInt
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

/-- (R2c-2) The compactor's disjunct, its pure part read without consuming it. -/
private theorem newServer_cmp_peek {a b : Prop} {Q : IProp GF} :
    iprop(⌜a⌝ ∨ ⌜b⌝ ∗ Q) ⊢ iprop(⌜a ∨ b⌝ ∗ (⌜a⌝ ∨ ⌜b⌝ ∗ Q)) := by
  iintro (%h | ⟨%h, HQ⟩)
  · isplitr
    · ipureintro; exact Or.inl h
    ileft; ipureintro; exact h
  · isplitr
    · ipureintro; exact Or.inr h
    iright; iframe HQ; ipureintro; exact h

/-- `a` and `b` copies of `P` are `a + b` (R-D1's readers, gathered for one retirement). -/
private theorem rep_join (P : IProp GF) (a b : Nat) :
    ⊢ ([∗list] _x ∈ List.replicate a (), P) -∗ ([∗list] _x ∈ List.replicate b (), P) -∗
      [∗list] _x ∈ List.replicate (a + b) (), P := by
  iintro Ha Hb
  rw [← List.replicate_append_replicate]
  iapply BigSepL.bigSepL_append.2
  iframe Ha Hb

/-- `a` copies of `P` and one more are `a + 1`. -/
private theorem rep_cons1 (P : IProp GF) (a : Nat) :
    ⊢ ([∗list] _x ∈ List.replicate a (), P) -∗ P -∗ [∗list] _x ∈ List.replicate (a + 1) (), P := by
  iintro Ha H
  rw [List.replicate_succ]
  iapply BigSepL.bigSepL_cons.2
  iframe H Ha

/-- (R8) `n` of the store's reader tokens are `n` single ones (`mvccReaders_split.law`). -/
private theorem mvccReaders_rep (hRS : mvcc.api.mvccReaders_split.law (GF := GF))
    (γ : mvcc.api.MvccName) :
    ∀ n, mvcc.api.mvccReaders (GF := GF) γ n ⊢
      [∗list] _x ∈ List.replicate n (), mvcc.api.mvccReaders γ 1
  | 0 => by
    rw [List.replicate_zero]
    iintro -
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | n + 1 => by
    iintro H
    icases (hRS γ n 1).1 $$ H with ⟨H, H1⟩
    ihave Hs := mvccReaders_rep hRS γ n $$ H
    iapply rep_cons1 _ _ $$ Hs H1

/-- `a` copies of `P` are `b`, at `a = b` (the premise after the copies, so that `a` is known when
it is proved). -/
private theorem rep_cast (P : IProp GF) (a b : Nat) :
    ⊢ ([∗list] _x ∈ List.replicate a (), P) -∗ ⌜a = b⌝ -∗ [∗list] _x ∈ List.replicate b (), P := by
  iintro H %h
  subst h
  iexact H

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
theorem NewServer.wp_proofG (on cmp : Bool)
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
    -- (2026-10-27) the node API's node specs, at the cluster's storage model
    (h9 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Ready.spec (GF := GF) (hG := hG))
    (h10 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Advance.spec (GF := GF) (hG := hG))
    -- (2026-10-30, the repair) `node.Stop` (until then `node.Advance.dynamicSpec`)
    (h10d : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Stop.spec (GF := GF) (hG := hG))
    (h11 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Tick.spec (GF := GF) (hG := hG))
    (h12 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReadIndex.spec (GF := GF) (hG := hG))
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
    -- (step 6 of the auth-mode merge) what the uber-applier's contracts with auth on are built from
    (hKit : uberKitM (GF := GF) (hG := hG) on)
    (h26 : mvcc.api.New.spec (GF := GF) (hG := hG))
    -- (R6, 2026-11-07, the `lean` merge) mvcc's API laws the boot uses (the store over its
    -- storage, `BootStore.boot_storage`; the store invariant, `bootStore_holds`; the readers'
    -- census of the error paths, `stop_census`; the compactor's revision getter)
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hfresh : mvcc.api.mvccImage_fresh.law (GF := GF))
    (hopen : mvcc.api.etcdStorage_open.law (GF := GF))
    (hrest : mvcc.api.backendRest_open.law (GF := GF))
    (hRS : mvcc.api.mvccReaders_split.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (hSR : mvcc.api.mvccStorageFor_rest.law (GF := GF))
    (h27 : newCorruptionChecker.spec (GF := GF) (hG := hG))
    (h28 : mvcc.api.watchableStore.HashStorage.spec (GF := GF) (hG := hG))
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
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (h42 : mvcc.api.watchableStore.Close.spec (GF := GF) (hG := hG))
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
    (h78 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Propose.spec (GF := GF) (hG := hG))
    (h79 : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (h80 : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (h81 : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (h82 : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (h83 : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (h84 : EtcdServer.ClusterVersion.spec (GF := GF) (hG := hG))
    (h85 : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (h86 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ApplyConfChange.spec (GF := GF) (hG := hG))
    -- (2026-10-30, the repair) the fresh `MemoryStorage`'s methods `StartNode`'s `bootStorage` runs
    -- (`srvMem_bootStorage`; until then `node.ApplyConfChange.dynamicSpec`)
    (h86d : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (h86e : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (h86f : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (h86g : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (h86h : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    -- (D21 M2) the inbound path: raft's `Step` and reports, the server's `Process` and co.
    (h87 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Step.spec (GF := GF) (hG := hG))
    (h88 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h89 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (h90 : EtcdServer.Process.spec (GF := GF) (hG := hG))
    (h91 : EtcdServer.IsIDRemoved.spec (GF := GF) (hG := hG))
    (h92 : EtcdServer.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h93 : EtcdServer.ReportSnapshot.spec (GF := GF) (hG := hG))
    -- (leases T3, 2026-10-25) the backend's delete, for the lessor's in the store's contract
    (h94 : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    -- (the lease-revoke plan, 2026-10-31) the lessor's `Revoke`, for `isApplyLessor`'s clause
    (h95 : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    -- (2026-11-01, J8a-5) the alarm store's `Get` with no alarm, for the uber-applier's construction
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    -- (R-D1, 2026-11-04) the error paths' `b.Close()` (until then `bootOk`'s `#Hclose`)
    (hBSC : bootstrappedServer.Close.spec (GF := GF) (hG := hG))
    -- (M2, `NewServer.spec`'s compaction mode) what only the compacting server uses: the compacting store's
    -- backend contract's specs, and the compactor's run precondition's (the server's `Rev` and
    -- `Compact`, `CompactEnv.lean`)
    (hLSR : cmp = true → backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : cmp = true → backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : cmp = true → backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hCmpS : cmp = true → EtcdServer.Compact.spec (GF := GF) (hG := hG)) :
    NewServer.specG (GF := GF) (hG := hG) on cmp := by
  haveI := Hp.1
  intro cfg U γ id ctxs ρ E₀ N Φs γn dir γd m HρRaft Hrule Hc0 Hch0 Hlog0 Hkcmp Hlgnn Hcbl Hmrb Hmto Hcb Hcon Hcmp0 HNx0
    Hbnd Hrb HrbN Hboot Hpfx HΦs Hfgp Hdirok HpU Hrnc Hdirs Hauthcfg Hlbc Hbco Hbcf Hbwb
  -- (2026-11-04, the lease-expiry plan's Part C) what the construction takes of the lease slot
  have Hlgon : on = true → ρ.rd.kv.lg = false := fun h => by
    rw [KVNames.lg_eq, lease.bootCfg_auth Hlbc h]; rfl
  have Hckok : ckptEffectsOk := lease.bootCfg_ckpt Hlbc
  have Hslg : ∃ m' : lease.Mode, lease.runCfg (GF := GF) ρ.rd.kv.lm m' := ⟨m, lease.bootCfg_run Hlbc⟩
  replace Hbnd : threadBound GF ≤ 2 ^ 28 := Hbnd
  letI : MemStorReg GF := ⟨γ.reg⟩
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
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hboot' := Hboot
  iunfold bootstrapContract at Hboot'
  wp_apply Hboot' $$ [Hrauth Hwdf] as %b %err Hb
  · iframe; iframe Hcfgro
    ipureintro; exact ⟨Hbco, Hbcf, Hbwb, Hdisk.1, Hdisk.2.2.2.2⟩
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
    iframe Htok
    ipureintro; exact ⟨rfl, Herr⟩
  subst Herr
  iNamed Hb
  -- (2026-11-03, the WAL's API) the opened WAL's parts (its records, metadata and the purge's right
  -- are not used yet: R2b-1's stage 4)
  -- (R2b-1 stage 3c) the WAL's durability allocated over the fresh records (`wal.bootOk_start`)
  imod wal.bootOk_start _ _ _ _ γ.cl $$ Hwal with
    ⟨%νw, #Hdur, Hwview, Hwok, Hwstop, Hwapp, #Hwlb, Hwalo, %HwalR, Hwmeta, Hwpurge, %HwDir⟩
  -- `bootOk` names two rows `Hmeta`: the storage's hard state, and the backend's
  irename : (memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) : IProp GF) =>
    Hmsmeta
  -- (2026-11-01, "bootOk's boot metadata") the fresh file's meta keys: `γA.m0 = (0, 0)`, no
  -- compaction recorded, the apply thread at `0`
  replace Hci : bk.ci' = ciIface cil ∧ γA.m0 = (W64 0, W64 0) := ⟨Hci, m0_of_metaEmpty HmEmpty Hm0⟩
  have HnoCmp : mvcc.noCmpData D := noCmpData_of_metaEmpty HmEmpty
  ihave Hthr := thr_fresh γA Hci.2 $$ Hthr
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
  have hNS := raftNode_of_StartNode (GF := GF) h8 h86d h85 h86e h86f h86g h86h h9 h10 h11 h10d h12 h87 h88
    h89 h78 h86
  obtain ⟨Hrcfg, Hrhb, Hrid, Hrnodup, Hr0, Hrmem, Hrvs, Hrbok⟩ := Hraft
  -- (2026-11-03, the whole-`bootOk` review, K) from the directory's bound (`Hdirps`); until then a
  -- conjunct of `bootOk`'s `Hraft`
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory's facts, from the
  -- transport's slot `rafthttp.bootCfg` (until then `bootOk`'s `Hdirps`)
  have Hdirps : (∀ f, dir f ≠ [] ↔ f ∈ ps) ∧ ps.length ≤ 2 ^ 20 :=
    ⟨fun f => by rw [← Hrvs]; exact rafthttp.bootCfg_mem Hdirs f,
      by rw [← Hrvs]; exact rafthttp.bootCfg_len Hdirs⟩
  have Hrpslen : (ps.length : Int) < 2 ^ 62 := by have := Hdirps.2; omega
  -- (rafthttp stage 6d) the raft loop's key to the transport's `Send` (`srvTrKey`), its name
  -- allocated now: the raft node's environment is built before the transport
  imod (srvSendKey_alloc (GF := GF)) with ⟨%γk, Hk⟩
  ihave Hnboot' : iprop(nodeBoot γ.cl srvClusterN ps ctxs cv.ID' ∗
      raftState γ.cl cv.ID' RaftState.init ∗ nodeVacant γ.cl cv.ID') $$ [Hnboot]
  · rw [← Hrvs, Hrid]; iexact Hnboot
  wp_apply (hNS γ (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk) (srvTrStopK γk)) bs.raft'
    bs.ss' bw.w' bc.cl' (DFrac.own 1) bv cv lok γs νw pv ps ctxs ρ.ids.issued)
    $$ [Hbv Hc Hfresh Hmsmeta Hend Hpeers Hnboot' Hwview Hwok]
    as %r ⟨%γrn, %rvr, %Hrnames, Hr, Hrtm, #HstepI, #Hsfresh, Hloop, Happly, Hrunh, Hinst, Hbv, -, #Hminv, Hmsmeta, Hrsc⟩
  · iframe Hbv Hc Hfresh Hmsmeta Hend Hpeers Hnboot' Hwview Hwok Hdur
    iframe #
    -- the pure premises: `bootOk`'s `Hraft` (`rnStartCfg`, its peers' facts), the heartbeat
    -- (`raftNode.bootCfg`), the directory's bound, the WAL read and the receipt bound
    ipureintro
    exact ⟨Hrcfg, by rw [Hrhb]; exact raftNode.bootCfg_heartbeat cfg Hrnc, Hrnodup, Hr0,
      Hrpslen, Hrvs, HwalR, by omega⟩
  clear Hrcfg
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
  -- (R2c) at the member's key: the claims' facts the server's family at its store's index
  wp_apply (h14 ρ.ids _ now srvFloorFacts E₀.γs.slog (by rw [Hpfx]; congr 1; rw [← Hid]))
    $$ [Hids] as %gen #Hgen0
  · iframe Hidc Hidk; iframe Hids
  ihave #Hgen : idGen ρ.ids gen (srvFloorFact E₀) $$ []
  · rw [show srvFloorFact (GF := GF) E₀ = srvFloorFacts E₀.γs.slog from rfl]
    iexact Hgen0
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
  have hMR : 2 ^ 29 + 2 ^ 28 + 100 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  have hM1 : 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by omega
  -- (D21 M2; rafthttp stage 6d) the transport's `lgMu` reader slots, one per concurrent call into
  -- the server's `Raft` (`Process`'s `Logger()`): `httpProcSlots` for the requests the member's raft
  -- handler serves
  have hHP : http.httpProcSlots = 2 ^ 29 := rfl
  icases replicate_takeN _ http.httpProcSlots _ (by omega) $$ Hlgrs with ⟨HlgServe, Hlgrs⟩
  -- (J8a-6, 2026-11-01, the user's decision; until then `2 ^ 23` slots for the peers' goroutines,
  -- eight each, and `2 ^ 22` for the remotes', four each, which the snapshots' `AddPeer`s consumed)
  -- `2 ^ 28` for the transport's pool (`raftPool`, a thread pool: `threadBound GF ≤ 2 ^ 28`), which
  -- the peers' receiving goroutines borrow from with their thread tokens
  icases replicate_takeN _ (2 ^ 28) _ (by omega) $$ Hlgrs with ⟨HlgPool, Hlgrs⟩
  imod raftPool_init (srvLgReader s) ⊤ (2 ^ 28) (by omega) $$ HlgPool with #HrPool
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
  obtain ⟨Hbe0, HbP, Hci0, HhP, HPwf, HPlim, HlP, HalB, HauB, HauUB, HauRB⟩ := Hbe
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
  -- (R6, 2026-11-07, the `lean` merge) the store's storage over mvcc's API (`BootStore.boot_storage`):
  -- the backend's current-backend variable `γbe` at the store's instance (the API's backend, in
  -- compaction mode: `{ d with cm := true }`, `d`'s names and parameters), half `bemu`'s, a quarter
  -- the apply thread's, a quarter the write budget's; the budget, whose stock backs the storage's
  -- write-back supply; the storage at the empty history; the client's rest
  imod (dghostVar_alloc (GF := GF) (bkKey ({ d with cm := true } : mvcc.KBReal))) with ⟨%γbe, Hγbe⟩
  icases (dghostVar_split (GF := GF) γbe (bkKey ({ d with cm := true } : mvcc.KBReal))
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)) $$ [Hγbe] with ⟨Hγbm, Hγbe⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hγbe
  icases (dghostVar_split (GF := GF) γbe (bkKey ({ d with cm := true } : mvcc.KBReal))
      (DFrac.own (1 : Qp).half.half) (DFrac.own (1 : Qp).half.half)) $$ [Hγbe] with ⟨HγbA, HγbW⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hγbe
  have Hkey0 : ∀ k, backend.dget D mvcc.keyName k = none := fun k => by
    have h := mvcc.dget_of_keyView HbP HD k
    simpa using h
  imod (boot_storage hfresh hopen hrest Hbnd N HrbN ({ d with cm := true } : mvcc.KBReal)
      (fun γB => batchLockInv γA (metaTM γB d.P)) D E₀ γbe HbP HlP rfl Hkey0 HnoCmp)
    $$ [Hnew Hlate HγbW]
    with ⟨%γp, #HWBp, #HWA0, HWreg, #Hstock, HstoF, #HB, #HSC, Hhook, Hrbo, HbkP, HrdA, Hopen, HrtA,
      Hwb⟩
  · isplitl [Hnew]
    · iExactEq Hnew; rfl
    isplitl [Hlate]
    · iexact Hlate
    isplitr
    · imodintro; iExactEq Hsz; rfl
    iexact HγbW
  -- (the instance's names and parameters are `d`'s)
  ihave #HB : backend.isBackend d.γB d.P (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P))
      d.be $$ [HB]
  · iExactEq HB; rfl
  ihave #HSC : backend.isStopChans d.γB d.P (mvcc.api.mvccW d.gx)
      (batchLockInv γA (metaTM d.γB d.P)) d.be $$ [HSC]
  · iExactEq HSC; rfl
  ihave Hhook : backend.plHook d.γB func.nil $$ [Hhook]
  · iExactEq Hhook; rfl
  ihave Hrbo : backend.rbOwn d.γB (backend.rbData d.P D) $$ [Hrbo]
  · iExactEq Hrbo; rfl
  ihave HbkP : backend.bkRPool d.γB d.P d.be $$ [HbkP]
  · iExactEq HbkP; rfl
  ihave HrdA : backend.rdAuth d.γB d.P d.be $$ [HrdA]
  · iExactEq HrdA; rfl
  ihave Hopen : backend.bOpen d.γB (1 : Qp).half $$ [Hopen]
  · iExactEq Hopen; rfl
  ihave Hwb : ownToks d.γB.wb 5 $$ [Hwb]
  · iExactEq Hwb; rfl
  rw [show (5 : Nat) = 1 + 4 from rfl]
  icases (ownToks_add 4 1 d.γB.wb).1 $$ Hwb with ⟨Hwl, Hwb⟩
  -- `lease.NewLessor`
  rw [Hbe0]
  -- the grant guard `srvGrantGuard` at the cluster's lease mode and the auth mode (D19n; the
  -- lease-grant plan's D1, until then `False`, D45): the lessor's `expiredC` delivers only in a
  -- granting cluster with auth off (the lease-expiry plan's X1)
  -- (D22, 2026-10-23) the rest buckets: the tracked buckets' half, at the fresh file's
  have hDl : ∀ n ∈ mvcc.restBuckets, ((backend.rbData d.P D).lookup n).getD ∅ = ∅ :=
    fun n hn => by rw [rbData_real_lookup d D n hn]; exact HDr.1 n hn
  wp_apply (h24 cfg.Logger' _ _ d (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P)) (1 : Qp).half
      (srvGrantGuard ρ.rd.kv.lg on) (fun _ => True) (backend.rbData d.P D) (decide (m = .mono))
      trivial HlP)
    $$ [Hopen Hwl Hrbo]
    as %l ⟨Hopen, Hrbo, %lp, %γl, %Hl, #Hlinv, #Hlmode, #Hlcfg, #Hlexp, #Hlgd, Hlrd, Hlown, HlEv, Hlrvk, Hro, #Hlck, HleOn, #Hlbe, Hlstop, #Hllk'⟩
  · iframe HB Hclok
    unfold backend.wbTok
    -- (2026-11-02, the backend-auth-split stage) at every bucket: `rbOwn` is `rbPart ⊤`, and the
    -- lessor gives the boot its tracked buckets idle (`rbOwnIn ⊤`)
    iunfold backend.rbOwn at Hrbo
    iframe Hopen Hwl Hrbo
    ipureintro; exact ⟨Hlgnn, Hckok, by simp, hDl go!"lease" (by decide)⟩
  -- (the lease-grant stage, 2.13) the lessor's live set's ghost variable at `[]`: one half to the
  -- boot's `leasesLive`, the other to the apply thread's image (`srvRest`'s leased arm, 3b)
  imod (ghostVar_alloc (GF := GF) ([] : List w64)) with ⟨%γlt, Hlt⟩
  -- (the lease-expiry plan's E3 (c)) the lessor's history starts empty: its first snapshot
  ihave #Hlrdinv : lease.lessorRdInv (GF := GF) γl $$ []
  · ihave #Hli := Hlinv
    iunfold lease.lessorInv at Hli
    icases Hli with ⟨-, -, -, #H⟩
    iexact H
  imod (lease.lessorAt_empty γl ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hlrdinv $HlEv]
    with ⟨#Hl0, HlEv⟩
  ihave ⟨Hlt1, HltS⟩ := (ghostVar_split_half (GF := GF) γlt 1 ([] : List w64)).1 $$ Hlt
  -- (the auth plan's E3zb) its `Lookup` at the guard `False`: no lease, and the weaker clause
  ihave #Hlnil : iprop(□ (⌜on = true⌝ → apply.lookupNil (lease.lessorIface lp))) $$ []
  · iintro !> %hon
    iapply (lookupNil_of_guard lp ρ.rd.kv.lg on (Or.inr hon)) $$ Hllk'
  ihave #Hllk := lookupOk_of_guard lp (srvGrantGuard ρ.rd.kv.lg on) $$ Hllk'
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
    wp_auto_lc 1
    wp_apply h3
    · ipureintro; exact Hlgnn
    -- (R-D1) `b.Close()` (deferred): the backend's whole open token, from the constructors' half,
    -- the pool's shares and the stock's (R8, 2026-11-07: the storage's, which no store took,
    -- `mvccStorageFor_rest.law`; the apply thread's read token's; the write budget's, no one
    -- registered, `srvWTPool_reclaim`)
    iunfold backend.bkRPool at HbkP
    icases HbkP with ⟨-, HoPs⟩
    imod hSR _ _ _ _ _ $$ HstoF with Hst
    ihave Hst : iprop([∗list] _x ∈ List.replicate (backend.rdStockN - 2) (),
        backend.bOpen (GF := GF) d.γB backend.rdOpen) $$ [Hst]
    · iExactEq Hst; rw [mvcc.api.etcdStorage_rest]
    iunfold apply.bkRT at HrtA
    icases HrtA with ⟨-, HoA⟩
    imod srvWTPool_reclaim ({ E₀ with γbe := γbe } : apply.AEnv GF) γp _ _ $$ [Hlc1 HWreg HγbA]
      with HoW
    · iframe Hlc1 HWreg
      isplitr
      · iapply HWBp; ipureintro; rfl
      iexact HγbA
    ihave HoW : backend.bOpen (GF := GF) d.γB backend.rdOpen $$ [HoW]
    · iExactEq HoW; rfl
    have hS := backend.rdStockN_val
    ihave Hshares := rep_cons1 _ _ $$ Hst HoA
    ihave Hshares := rep_cons1 _ _ $$ Hshares HoW
    ihave Hshares := rep_cast _ _ backend.rdStockN $$ Hshares []
    · ipureintro; omega
    ihave HoO1 : backend.bOpen (GF := GF) d.γB 1 $$ [Hopen HoPs Hshares]
    · iapply (backend.bOpen_one_pool d.γB).2
      iframe Hopen HoPs Hshares
    ipersist Hb
    ipersist Hsto
    ipersist Hbk
    wp_apply (hBSC b bs sto bk d.γB d.P (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P))
      d.be) $$ [HoO1]
    · iframe Hb Hsto Hbk HB HSC HoO1
      ipureintro; exact Hbe0
    iapply HΦ
    ileft
    iframe Htok
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
  -- `mvcc.New` over the storage `boot_storage` opened (R8, 2026-11-07: `mvcc.api.New.spec`, in place of
  -- `server_kv_watchable_ofM`): the watchable store at the boot instance `{ d with cm := true }`, its
  -- state at `mvccStart`, its open token, its backend's whole share, its reader tokens, the range
  -- deleter
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨Hlr2, Hlgrs⟩
  wp_apply h19 $$ [Hlr2] as ⟨-, Hlr2⟩
  · iframe lg; iframe Hlr2; ipureintro; exact Hlgnn
  (try wp_auto)
  subst Hl
  ihave #Hmvpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hisl := lease.isLessor_of_lessorInv h49 h50 h51 h52 lp γl $$ [$Hlspkg $Hlinv]
  -- the lessor's reader slots: one for the store, one for the apply thread's lease owner (D14i)
  icases replicate_take1 _ _ hM1 $$ Hlrd with ⟨Hlrd, Hlrds⟩
  icases replicate_take1 _ _ (by omega) $$ Hlrds with ⟨Hlrd2, Hlrds⟩
  -- (the lease-src plan) the rest in the lessor's reader pool, which the lease service's calls
  -- borrow from with their thread tokens (`threadBound GF ≤ 2 ^ 28`)
  imod lease.lessorRdPool_init γl ⊤ _ (by omega) $$ Hlrds with #HlPool
  have HstN := backend.rdStockN_val
  have hsv : mvcc.api.storageVal (mvcc.api.etcdStorage ({ d with cm := true } : mvcc.KBReal)) =
      srvBeIface d.be := mvcc.api.etcdStorage_val _
  haveI : ReceiptBoundLe GF (2 ^ 48) := ⟨by omega⟩
  have hNew := fun c r0 => h26 cfg.Logger' (lease.lessorIface lp) c
    (mvcc.api.etcdStorage ({ d with cm := true } : mvcc.KBReal)) (batchLockInv γA (metaTM d.γB d.P))
    γl r0
  simp only [hsv] at hNew
  wp_apply (hNew _ _ Hcbl) $$ [HstoF Hlrd Hro]
    as %ws ⟨%γm, %Hγl, #HisKV, Hst0, Hopn, HmB, Hrds, Hrdat⟩
  · iframe #; iframe HstoF Hlrd Hro
  clear hNew hsv
  -- (R8) the store invariant at the boot (`bootStore_holds`): the store's state at `mvccStart`,
  -- the server's store names fresh, raft's committed log's empty floor
  ihave #Hrlb0 : srvRLogLb ρ.rd.raft [] $$ []
  · ihave #Hsrl' := Hsrl
    iunfold srvRaftLogInv at Hsrl'
    icases Hsrl' with ⟨-, -, #H, -⟩
    iexact H
  haveI : Persistent (srvApi.kvStoreInv (GF := GF) (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws) γm ρ.rd on E₀.γs) := by
    rw [srvApi.kvStoreInv_eq]; exact srvApi.kvStoreInvG_persistent Hp _ _ _ _ _
  haveI hCpP : ∀ c, Persistent (kvCpOk (GF := GF) ρ.rd.kv c) := fun c => by
    unfold kvCpOk; infer_instance
  haveI hCpT : ∀ c, Timeless (kvCpOk (GF := GF) ρ.rd.kv c) := fun c => by
    unfold kvCpOk; infer_instance
  haveI := srvApi.kvStoreInvG_persistent Hp (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws) γm (srvApi.kvNx ρ.rd on)
      (kvCpOk ρ.rd.kv) E₀.γs
  imod (srvApi.bootStore_holds Hp (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws) γm ρ.rd on E₀.γs
      (by cases on <;> exact (show _ = ρ.rd.kv.log0 from rfl).trans Hlog0))
    $$ [$HisKV $Hst0 $Hkvs $Hrlb0] with ⟨#HkvS, Hw0, Hcr0⟩
  -- (R8) the store's reader tokens, split: the stop's (`srvKeepRdN`), the request slots' 64, the
  -- watch service's 64, the compactor's or the stop's 1, the apply thread's 1
  have hRN : mvcc.api.mvccReaderN = srvKeepRdN + 64 + 64 + 1 + 1 := by
    unfold srvKeepRdN; rw [mvcc.api.mvccReaderN_eq]; omega
  ihave Hrds : mvcc.api.mvccReaders γm (srvKeepRdN + 64 + 64 + 1 + 1) $$ [Hrds]
  · rw [← hRN]; iexact Hrds
  icases (hRS γm _ 1).1 $$ Hrds with ⟨Hrds, HrdApp⟩
  icases (hRS γm _ 1).1 $$ Hrds with ⟨Hrds, HrdC⟩
  icases (hRS γm _ 64).1 $$ Hrds with ⟨Hrds, HrdWatch⟩
  icases (hRS γm _ 64).1 $$ Hrds with ⟨HrdKeep, HrdServe⟩
  -- `newCorruptionChecker(lg, srv, srv.kv.HashStorage())`
  wp_apply (h28 ws γm) $$ [] as %hst -
  · iframe #
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
  -- (the auth-on snapshot plan's P5) the auth buckets idle to the kit, the others kept; in the mode
  -- `on` a quarter of the open token and the auth share of the reader slots to the kit too
  -- (`authKitIn`), the apply thread keeping `srvOpenQ M`
  icases (backend.rbOwnIn_split_compl (GF := GF) d.γB authBkts _).1 $$ Hrbo with ⟨HrbA, Hrbo⟩
  icases authKitIn_take M d $$ [Hopen HrdA] with ⟨HkIn, Hopen⟩
  · iframe Hopen; iunfold authRdSlots; iexact HrdA
  ihave HKt' := HKt $$ %cfg.Logger' %ab %abl %d %(mvcc.api.mvccW d.gx)
    %(batchLockInv γA (metaTM d.γB d.P)) %(srvOpenQ M) %((backend.rbData d.P D).insert go!"lease" ∅)
  wp_apply HKt'
    $$ [HK Hopen Hhook Hwa HrbA HkIn]
    as %ast ⟨Hopen, Hhook, HkOut, %RD, %astl, %Hastl, HauthOn, HRDs, #HisReq, #HisAuth,
      #HstL, #HstLb, #HstPub, #HbBk, HAres, HcapM, #HAb, #HauR, #HauC, #HauSK, #Hbc⟩
  · iframe Habbe Hablg HB
    iframe Hapkg HK Hopen Hhook Hwa HrbA HkIn
    ipureintro
    refine ⟨Hlgnn, Htpnn, Haufit, Hab, ⟨?_, ?_, ?_⟩, HauB, HauUB, HauRB⟩
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hDl go!"auth" (by decide)
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hDl go!"authUsers" (by decide)
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hDl go!"authRoles" (by decide)
  (try wp_auto)
  ihave Hrbo := authKitOut_join M d _ $$ [Hrbo HkOut]
  · iframe Hrbo HkOut
  -- (E3u) the start's auth state published, for the applied index's invariant
  imod authApplyResPre_publish M astl _ _ RD $$ HstPub HAres with ⟨HAres, #Hpub0⟩
  -- the compactor (`if num := cfg.AutoCompactionRetention; num != 0 { srv.compactor, err =
  -- v3compactor.New(…, srv.kv, srv) … }`): off, none; on (M2), `v3compactor.New`'s (in revision
  -- mode, no error), over the server's KV and itself, the resource its calls borrow `srvCompactR`'s
  -- (at the names here: the environment is built below)
  ipersist Logger
  ipersist AutoCompactionMode
  ipersist num
  ipersist kv
  wp_join iprop(err_ptr ↦ GoInterface.nil ∗ srv_ptr ↦ s ∗ ∃ cpv : GoInterface,
      s.[EtcdServer, go!"compactor"] ↦ cpv ∗ compactorOk cpv ∗
      (⌜cpv = GoInterface.nil⌝ ∨ ⌜cmp = true⌝ ∗
        -- (K1, 2026-11-04) the mode's permit, from the compactor's slot where it is built
        ⌜if cfg.AutoCompactionMode' = go!"revision" then
            0 ≤ sint.Z cfg.AutoCompactionRetention' ∧
              ((ρ.rd.kv.cret : Nat) : Int) ≤ sint.Z cfg.AutoCompactionRetention'
          else ρ.rd.kv.cret = 0⌝ ∗ ∃ (T : IProp GF) (γf : GName),
        v3compactor.compactorOk cpv T (v3compactor.runPre
          ⟨srvRevLb ({ E₀ with kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, Nx := srvApi.kvNx ρ.rd on, RD := RD } : apply.AEnv GF), interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws,
            interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s,
            srvCompactR s ({ E₀ with kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, Nx := srvApi.kvNx ρ.rd on, RD := RD } : apply.AEnv GF)⟩
          (v3compactor.modePermit cfg.AutoCompactionMode' (srvRevLb ({ E₀ with kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, Nx := srvApi.kvNx ρ.rd on, RD := RD } : apply.AEnv GF))
            (sint.Z cfg.AutoCompactionRetention') γf)) ∗ T))
    with [err srv compactor] as ⟨err, srv, %cpv, compactor, #Hcpok, Hcpt⟩
  · -- `num == 0`: no compactor
    iframe err srv
    iexists _
    iframe compactor
    isplitr
    · iunfold compactorOk; ileft; ipureintro; rfl
    ileft; ipureintro; rfl
  · -- `num != 0`: by the compactor's slot (`v3compactor.bootCfg_build`), the compaction mode on,
    -- `v3compactor.New` in revision or periodic mode, and the mode's permit
    obtain ⟨hcmpT, Hmode', hPer, Hcrm⟩ := v3compactor.bootCfg_build Hcb
      (by first | exact Hif | simpa using Hif | (intro h; exact Hif (by simp [h])))
    subst hcmpT
    ihave #Hcppkg : isPkgInit (PROP := IProp GF)
        pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor $$ []
    · iPkgInit
    have hNew := h31 cfg.Logger' cfg.AutoCompactionMode' cfg.AutoCompactionRetention'
        ⟨srvRevLb ({ E₀ with kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, Nx := srvApi.kvNx ρ.rd on, RD := RD } : apply.AEnv GF), interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws,
          interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s,
          srvCompactR s ({ E₀ with kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, Nx := srvApi.kvNx ρ.rd on, RD := RD } : apply.AEnv GF)⟩
        hPer
    simp only at hNew
    wp_apply hNew as %cp %cperr Hcp
    icases Hcp with (⟨%Hcpe, %T, %γf, #Hcpo, HT⟩ | %Hcpe)
    rotate_left
    · rcases Hmode' with h | h
      · exact absurd h Hcpe.2.2
      · exact absurd h Hcpe.2.1
    subst Hcpe
    (try wp_auto)
    isplitr
    · ipureintro; rfl
    iframe err srv
    iexists cp
    iframe compactor
    isplitr
    · iunfold compactorOk; iright; iexists T, _; iexact Hcpo
    iright
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact Hcrm
    iexists T, γf
    iframe Hcpo HT
  -- the auth store's reader slots: one for the auth applier (2026-11-01, J8a; since P6.2 the apply
  -- thread's auth row's, what the store's `Recover` reads a snapshot's backend with), one for the
  -- KV's (D14i)
  -- (P1/N4) of the auth store's supply, `authRdN - 1` tickets
  have hAN : backend.authRdN = 2 ^ 28 + 128 := rfl
  iunfold authRdSupply at HRDs
  icases replicate_take1 _ _ (by omega) $$ HRDs with ⟨HRD, HRDs⟩
  icases replicate_take1 _ _ (by omega) $$ HRDs with ⟨HRD2, HRDs⟩
  -- (D19g (b)) the auth store's reader slots for request goroutines
  icases replicate_takeN _ 64 _ (by omega) $$ HRDs with ⟨HRDs, HRDstock⟩
  -- (M2) one for the compactor's calls (`srvCompactR`)
  icases replicate_take1 _ _ (by omega) $$ HRDstock with ⟨HRDC, HRDstock⟩
  -- `srv.restoreAlarms()`
  rw [show (2 : Nat) = 1 + 1 from rfl]
  icases (ownToks_add 1 1 d.γB.wb).1 $$ Hwb with ⟨Hwb, Hwal⟩
  ihave Hrbo := backend.rbOwnIn_part (GF := GF) _ _ _ $$ Hrbo
  wp_apply (h32 s cfg.Logger' d (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P)) (srvOpenQ M) _
      (DFrac.own 1) (kitSet M) (((((backend.rbData d.P D).insert go!"lease" ∅).insert go!"auth" authBoot).insert
        go!"authUsers" ∅).insert go!"authRoles" ∅)
      (kitSet_of M _ (by simp [authBkts, auth.authBkts])) HalB)
    $$ [Hopen Hwal alarmStore be Hrbo HbkP Htok]
    as %aerr ⟨%Haerr, Hopen, HbkP, Htok, Hrbo, be, %alst, %Halnn, alarmStore, #HalS, HalOn, #HalA⟩
  · iframe #
    unfold backend.wbTok
    rw [← Hbe0]
    -- (2026-11-02, the backend-auth-split stage) at every bucket (P5: the mode's, `kitSet`), with
    -- the backend's reader pool and the constructing thread's token, given back
    iframe Hopen Hwal alarmStore be Hrbo HbkP Htok
    ipureintro
    refine ⟨Hlgnn, ?_⟩
    rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
      GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide)]
    exact hDl go!"alarm" (by decide)
  -- the rest buckets after the constructors: the boot state's
  rw [restBootBk_of_fresh d D HDr]
  clear hDl HDr
  -- (2026-11-02, the backend-auth-split stage) `NewAlarmStore` returns no error (the alarm bucket
  -- is empty), so `restoreAlarms` does not; the tracked buckets idle, as the rest resource holds
  -- them below
  subst Haerr
  (try wp_auto)
  -- `srv.uberApply = srv.NewUberApplier()`: its contract given once the hook is installed
  ipersist alarmStore
  ipersist authStore
  ipersist lessor
  ipersist cluster
  ipersist consistIndex
  ipersist QuotaBackendBytesS
  ipersist WarningApplyDurationS
  -- (2026-11-01, J8a-5) the store has no alarm: `Get` returns none under the user's half
  ihave #Hv3apkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  ihave #Hget := alarmGetIs_empty hAG alst d.be $$ [$Hv3apkg $HalS]
  wp_apply (h33 s cfg.Logger' alst bc.cl' _ _ _ _ _ _ cfg.QuotaBackendBytes'
      cfg.WarningApplyDuration' (DFrac.own 1) (alarmEmpty alst d.be) true Hbuq) $$ [be HalOn]
    as %ua ⟨be, HalOn, %up, %uopts, %Hua, %Huopts, Hulate⟩
  · iframe #; iframe be HalOn
  ihave HalOn := alarmEmpty_beOn alst d.be $$ HalOn
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
  wp_apply (h35 d.γB d.P (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P)) d.be (srvOpenQ M) func.nil hook)
    $$ [Hopen Hhook Hwb] as ⟨Hopen, Hhook⟩
  · iframe HB
    unfold backend.wbTok
    iframe Hopen Hhook Hwb
  imod (backend.plHook_persist (GF := GF) d.γB hook) $$ Hhook with #Hhook
  -- the backend and its hook at the store's instance (`boot_storage`'s `{ d with cm := true }`,
  -- `d`'s names and parameters; R8: the store over mvcc's API, always compacting)
  ihave #HBs : backend.isBackend ({ d with cm := true } : mvcc.KBReal).γB
      ({ d with cm := true } : mvcc.KBReal).P (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P))
      ({ d with cm := true } : mvcc.KBReal).be $$ []
  · iExactEq HB; rfl
  ihave #Hhooks : backend.plHookRO ({ d with cm := true } : mvcc.KBReal).γB hook $$ []
  · iExactEq Hhook; rfl
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
  obtain ⟨Hrn1, Hrn5, Hrn6, Hrn7, Hrn8, Hrnν, Hrna0, Hrn10, Hrn11, Hrn12, Hrn13, Hrn14, Hrn15, Hrnwal⟩ := Hrnames
  -- (2026-10-27) the cluster's kind, at the wrapper's names
  ihave #Hkind : srvClusterOk γrn.srv $$ []
  · ihave #Hsrl' := Hsrl
    iunfold srvRaftLogInv at Hsrl'
    icases Hsrl' with ⟨-, #Hcl0, -⟩
    rw [srvClusterOk_congr γrn.srv ρ.rd.raft (by simp [RNNames.srv, Hrn1, HρRaft])]
    iexact Hcl0
  -- (D21 M2) what the transport's calls into the server read (`srvProcOk`): the wrapper's
  -- fixed fields split off its struct (the node's among them), the member id, the stats
  imod rnFixed_split (srvRAddr s) rvr $$ r with ⟨#Hfix, Htrf, HlatestTs⟩
  ihave #HNodeC : rnNodeAddr (srvRAddr s) ↦□ rnNodeIface γrn $$ []
  · rw [← Hrn14]
    iunfold rnFixed at Hfix
    iNamed Hfix
    iexact NodeC
  -- (2026-10-31) the WAL's open token (`bootOk`'s) at the wrapper's storage, split: the raft
  -- loop's half and the apply side's
  ihave Hwt : rnWalTok (srvRAddr s) 1 $$ [Hwalo]
  · iunfold rnFixed at Hfix
    iNamed Hfix
    iunfold rnWalTok
    iexists rvr.raftNodeConfig'.storage'
    iframe storageC
    rw [Hrnwal]; iexact Hwalo
  icases rnWalTok_split (srvRAddr s) $$ Hwt with ⟨Hwth, Hwtl⟩
  -- (2026-11-03, R2b-1 stages 5-6) the shares: the apply side's with its token and the
  -- durability invariant, the loop's with the stop's claim, the metadata and the purge's right
  ihave Hwth : rnWalTokA γrn (srvRAddr s) (1 : Qp).half $$ [Hwth Hwapp]
  · iunfold rnWalTok at Hwth
    icases Hwth with ⟨%st0, #Hst0, Hwo⟩
    iunfold rnWalTokA
    iexists st0
    iframe Hst0 Hwo
    rw [Hrnν]; iframe Hwapp
    iunfold rnFixed at Hfix
    iNamed Hfix
    icombine storageC Hst0 gives %Hsteq
    have Hsteq' : st0 = rvr.raftNodeConfig'.storage' := by
      first | exact Hsteq.symm | exact Hsteq.2.symm
    rw [Hsteq', Hrnwal, Hrn1]; iexact Hdur
  ihave Hwtl : rnWalTokL γrn (srvRAddr s) $$ [Hwtl Hwstop Hwmeta Hwpurge]
  · iunfold rnWalTokL
    rw [Hrnν]
    iframe Hwtl Hwstop
    iunfold rnFixed at Hfix
    iNamed Hfix
    iexists rvr.raftNodeConfig'.storage', _
    iframe storageC
    rw [Hrnwal]
    -- (R2b-3b) the metadata names the member, the wrapper's id
    have hidr : γrn.id = id := by first | rw [Hrn5, Hrid] | rw [Hrn5, Hrid, Hid]
    rw [hidr]
    iframe Hwmeta Hwpurge
  ipersist memberID
  ipersist beHooks
  ipersist stats
  ihave #Hprocok : srvProcOk γn s id γd $$ []
  · iunfold srvProcOk
    iexists cfg.Logger', bc.cl', sstats, γrn
    rw [← Hid]
    iframe stats memberID HNodeC cluster lg HstepI Hrc Hkind
    ipureintro
    exact ⟨Hlgnn, by rw [Hrn5, Hrid, Hid], Hssnn, by rw [Hγn.1, Hrn1],
      by rw [Hrn1]; (first | (rw [Hid]; exact Hsloc) | (rw [← Hid]; exact Hsloc) | exact Hsloc)⟩
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
  have Hturls : trURLsOk (netRh γn) id U.peer :=
    trURLsOk_of_dir γn dir Hγn.2 Hdirok ps Hdirps.1 id (Hrid ▸ Hrmem) U.peer HpU
  wp_apply (h38 γn t _ (srvLgReader s) γd (srvSnapRm γt ρ.rd) U.peer (ps.filter (· ≠ id)))
    $$ [«$r0» Hlsf] as %terr Htres
  · iframe «$r0»
    simp only
    rw [Hid]
    iframe Hnro Hss Hsdir HpU Hnet Hlsi Hlsf HrPool
    ipureintro; refine ⟨Hlgnn, Hssnn, Hlsnn, ?_, Hdid, HLnd, Hturls⟩ <;> first | rfl | trivial
  icases Htres with (%Hterr | ⟨%Hterr, %c, %Hc, Htlive, Htoks, #HtrNet, #Htrr, -⟩)
  · -- the transport could not start: the error returned, the store and `b` closed
    cases terr with
    | nil => exact absurd rfl Hterr
    | ok ei => ?_
    wp_auto_lc 1
    -- (R8) `kv.Close()` over mvcc's API (`KV.Close.contract`): the open token for the closed store
    wp_apply (h42 ws γm) $$ [Hopn] as Hcld
    · iframe #; iframe Hopn
    (try wp_auto)
    -- (R-D1; R8 over mvcc's API) `b.Close()` (deferred, after `kv.Close()`): the backend's whole
    -- open token, by the census (`stop_census_open`): every reader token of the store back, with
    -- the closed store and its backend share, gives the storage's shares; the apply thread's read
    -- token's share, the write budget's (no one registered, `srvWTPool_reclaim`)
    ihave Hrds : mvcc.api.mvccReaders γm (srvKeepRdN + 64) $$ [HrdKeep HrdServe]
    · iapply (hRS γm _ _).2; iframe HrdKeep HrdServe
    ihave Hrds : mvcc.api.mvccReaders γm (srvKeepRdN + 64 + 64) $$ [Hrds HrdWatch]
    · iapply (hRS γm _ _).2; iframe Hrds HrdWatch
    ihave Hrds : mvcc.api.mvccReaders γm (srvKeepRdN + 64 + 64 + 1) $$ [Hrds HrdC]
    · iapply (hRS γm _ _).2; iframe Hrds HrdC
    ihave Hrds : mvcc.api.mvccReaders γm (srvKeepRdN + 64 + 64 + 1 + 1) $$ [Hrds HrdApp]
    · iapply (hRS γm _ _).2; iframe Hrds HrdApp
    ihave Hrds : mvcc.api.mvccReaders γm mvcc.api.mvccReaderN $$ [Hrds]
    · rw [hRN]; iexact Hrds
    iunfold apply.bkRT at HrtA
    icases HrtA with ⟨-, HoA⟩
    imod srvWTPool_reclaim ({ E₀ with γbe := γbe } : apply.AEnv GF) γp _ _ $$ [Hlc1 HWreg HγbA]
      with HoW
    · iframe Hlc1 HWreg
      isplitr
      · iapply HWBp; ipureintro; rfl
      iexact HγbA
    -- the auth store abandoned: with every reader's ticket and the apply thread's resources, the
    -- realization's share of the open token back (`authAbandonM`), the constructors' half again
    ihave HRDa := rep_cons1 _ _ $$ HRDstock HRDC
    ihave HRDa := rep_join _ _ _ $$ HRDa HRDs
    ihave HRDa := rep_cons1 _ _ $$ HRDa HRD2
    ihave HRDa := rep_cons1 _ _ $$ HRDa HRD
    ihave HRDa := rep_cast _ _ (backend.authRdN - 1) $$ HRDa []
    · ipureintro; rw [hAN]
    ihave HRDa : authRdSupply RD $$ [HRDa]
    · unfold authRdSupply; iexact HRDa
    iunfold authAbandonM at HAb
    imod HAb $$ %(auth.bump auth.bootState) HRDa HAres with HAo
    ihave Hhalf := authOpenM_join M d $$ [Hopen HAo]
    · iframe Hopen HAo
    iunfold backend.bkRPool at HbkP
    icases HbkP with ⟨-, HoPs⟩
    ihave Hcen := stop_census_open hCR γm ({ d with cm := true } : mvcc.KBReal) 1
      (batchLockInv γA (metaTM d.γB d.P)) $$ [HoA HoW Hhalf HoPs]
    · iframe HoA Hhalf HoPs
      iExactEq HoW; rfl
    imod Hcen $$ [Hcld Hrds HmB] with ⟨HoO1, -⟩
    · iframe Hcld Hrds HmB
    ipersist Hb
    ipersist Hsto
    ipersist Hbk
    wp_apply (hBSC b bs sto bk d.γB d.P (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P))
      d.be) $$ [HoO1]
    · iframe Hb Hsto Hbk HB HSC HoO1
      ipureintro; exact Hbe0
    iapply HΦ
    ileft
    iframe Htok
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
  -- transport's live state), each other member's so far
  ihave IH2 : iprop(∃ (n : w64) (mm : Loc) (L : List w64), "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mm ∗
      "Htlive" ∷ trLive γn t c L ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z msl.len ∧ L.length ≤ (sint.Z n).toNat⌝ ∗
      "%Hcov" ∷ ⌜∀ (k : Nat) (p : Loc × w64), k < (sint.Z n).toNat → mps[k]? = some p →
        p.2 ≠ id → p.2 ∈ L⌝) $$ [i m Htlive]
  · iexists W64 0, _, []
    iframe i m Htlive
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
      "Htlive" ∷ trLive γn t c L ∗
      "%Hcov" ∷ ⌜∀ f, (netRh γn).member f → f ≠ id → f ∈ L⌝))
    at (App (App (App (Val doFor) _) _) _) with [b Hb nodeID tr Hmsl Hmso IH2]
    as ⟨%L, b, Hb, nodeID, tr, Hmsl, Hmso, Htlive, %Hcov⟩
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
        wp_apply (h41 γn t c L px.2 mpu (DFrac.own 1) mpus Hne Hpl Hown
            (by rw [Hcl]; exact fun h => Hpid h.symm) Hpm) $$ [Htlive Hmpus]
          as ⟨Htlive, Hmpus⟩
        · iframe Htlive Hmpus
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
        wp_for_post
        iframe
        iexists n + W64 1, _, L ++ [px.2]
        iframe
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
      ({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) E₀ :=
    -- (R8) the stand-in's witness the server's (`specG`'s premise `E₀.Nx = kvNxM on ρ.rd`)
    ⟨rfl, HNx0.symm, rfl, rfl⟩
  -- the transport, started: (rafthttp stage 6d) frozen, every other member a peer; the network's
  -- transport, its `Send` with the raft loop's key (fixed to it now)
  -- (D22 J-T, 2026-10-27: until then frozen here, D41) the transport stays live, the apply
  -- thread's (`srvApRes`). (Until J8a-7, 2026-11-01, opened here and the no-remote tokens
  -- collected, `srvTrTok`'s.)
  ihave #Hst : trState γn t c $$ [Htlive]
  · iunfold trLive at Htlive; icases Htlive with ⟨#H, -⟩; iexact H
  have HcLm : ∀ f, f ∈ c.L ↔ f ∈ ps ∧ f ≠ id := by
    intro f; rw [HcL, List.mem_filter]; simp
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
  ihave #Hrlb := Hrlb0
  -- (R8) the writer's facts at the boot (`srvApi.writer_facts`): a floor of the store's log
  ihave #HkvSG : srvApi.kvStoreInvG (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws) γm (srvApi.kvNx ρ.rd on)
      (kvCpOk ρ.rd.kv) E₀.γs $$ []
  · iExactEq HkvS; rw [srvApi.kvStoreInv_eq]; cases on <;> rfl
  imod srvApi.writer_facts (srvApi.kvNx ρ.rd on) (kvCpOk ρ.rd.kv) Hp Hr _ γm E₀.γs [[], []] (-1)
    $$ HkvSG Hw0 with ⟨Hw0, #Hlb0, #Hnx0, -, -⟩
  -- the indices
  imod (srvIndices_allocM on s
      ({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) ρ.rd ⊤
      (by rw [HρRaft]))
    $$ [appliedIndex] [committedIndex] [term] Hap Hcm Hlogs Hpend [] Hrlb []
    with ⟨#Hai, Haown, #Hal0, #Hcmi, Hcmown, #Hti⟩
  · iapply hU64; iexact appliedIndex
  · iapply hU64; iexact committedIndex
  · iapply hU64; iexact term
  · rw [Hlog0]; iexact Hlb0
  · iapply appliedPubM_zero on _ ρ.rd (by rw [HρRaft]) $$ Hrlb
    iExactEq Hpub0
    rfl
  -- the KV invariants
  imod (kvCertInvM_alloc on ρ.rd.raft ρ.rd.kv srvAuthSt0 ⊤ (by rw [Hlog0]; simp)) $$ [Hcok] Hkhi1 Hrlb
    with #Hkci
  · iexact Hcok
  imod authHistTie_alloc (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF) ρ.rd astl ⊤ $$ HcapM Hrlb
    with #Htie
  -- the mints
  have hργ : ρ.raft.raft = γ := by simp only [ReqNames.raft, HρRaft]
  imod (srvMintInv_alloc ρ ⊤) $$ [] [] with #Hmint
  · iexact Hpmint
  · iexact Hrdctx
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
  icases replicate_takeN _ 64 _ (by omega) $$ Hltslots with ⟨Hlts, Hltslots⟩
  -- (M2) one for the compactor's calls (`srvCompactR`)
  icases replicate_take1 _ _ (by omega) $$ Hltslots with ⟨HltC, HltRest⟩
  -- (D22 receiver epochs, S7b) half of `s.be` the apply thread's (`srvBeOwn`); until then (D19i
  -- part 2) kept out of `bemu` for good, the storage version monitor's
  icases (typedPointsto_dfractional (GF := GF) (srvBeAddr s) (srvBeIface d.be)).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [be] with ⟨be, beA⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact be
  imod sync.init_RWMutex (bemuP s γbe) (E := ⊤) (srvBemuAddr s) $$ [be Hγbm] bemu with Hbmslots
  · inext; iunfold bemuP; iexists ({ d with cm := true } : mvcc.KBReal)
    iframe be Hγbm
    iunfold srvBeRO
    iexists d.gx, batchLockInv γA (metaTM d.γB d.P); iexact HBs
  icases replicate_take1 _ _ hM1 $$ Hbmslots with ⟨Hbmr, Hbmslots⟩
  -- (D19g (b)) `v3rpc.Server`'s reader slot of `bemu`
  icases replicate_take1 _ _ (by omega) $$ Hbmslots with ⟨Hbmr2, Hbmslots⟩
  -- (D22g (A)) the quota checks' reader slots of `bemu`, for request goroutines
  icases replicate_takeN _ 64 _ (by omega) $$ Hbmslots with ⟨Hbms, Hbmslots⟩
  -- (D19i part 2) the storage version monitor's
  icases replicate_take1 _ _ (by omega) $$ Hbmslots with ⟨HbmSV, -⟩
  -- the raft node, its transport installed
  ihave #Henv : rnEnvOk (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk) (srvTrStopK γk)) γrn $$ []
  · iapply (rnEnvOk_of_clusterM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) γrn
      (by rw [Hrn1, hργ]) (by rw [Hrn6]; simp only [ReqNames.raft, HρRaft])
      (by rw [Hrn6]; simp [ReqNames.raft, HρRaft]) (by simp only [ReqNames.raft, HρRaft])
      (by rw [Hrn1, Hrule, Hc0]) id (srvTrKey γn γk) (srvTrStopK γk)
      (by rw [Hrn5, Hrid]))
    iframe Hkvinv Hsrl
    iapply clusterWorkloadOkM_of on ρ E₀
    iframe Hkvinv Hsrl HNZ0
  -- (R2b-3d stage 5c) the `transport` field read-only before the install: the environment's
  -- `Stop` names it (`srvTrStop`)
  ipersist Htrf
  imod Hinst $$ %(srvRAddr s) %s %(interface.mkOk (go.GoType.PointerType api.rafthttp.Transport.ty) #t)
    [Henv] [Hcmi] [] [] [] [HlatestTs] [] [Hrtm] with ⟨#Hrn, Hrdone, #Hnodef, #Hprop, -⟩
  · iexact Henv
  · iexact Hcmi
  · simp only [srvErM]; iexact Hrdctx
  · iexact Hfix
  · iexact Htrf
  · iexact HlatestTs
  · -- (D21 M2) the raft wrapper's messages carry their bundle into the network
    ihave #Htrall' : netTransport γn id (transportIface t)
        (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk) (srvTrStopK γk)).S
        (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk) (srvTrStopK γk)).ST $$ []
    · rw [show (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk) (srvTrStopK γk)).S = srvTrKey γn γk
        from rfl,
        show (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk) (srvTrStopK γk)).ST = srvTrStopK γk
        from rfl]
      -- (R2b-3d stage 5c) its `Stop` at the server's stop right (`srvTrStop`), the apply thread's
      -- live transport (until then `False`, `Htrall`'s)
      iapply (netTransport_srvTrStop hPeerStop hRemoteStop γn id γk (s, t, c.lid, c.γd, c.γs, c.γr) s t
        rfl rfl)
      iframe Hrhpkg Hkx Htrf Htrall
    iapply isRNTransport_of_net γn id $$ [] Htrall'
    iintro !> %m HM
    simp only [srvErM]
    rw [Hγn.1, ← hργ]
    iapply (srvMsgNet_bundle _ id m) $$ [HM]
    iexact HM
  · iexact Hrtm
  -- (D17d) `run`'s snapshot contract, from the storage's snapshot token
  ihave Hgap : srvBuildGap s γrn (W64 0) (W64 0) $$ [Hsnone]
  · iunfold srvBuildGap
    rw [Hrn8, show γrn.node.reg = MemStorReg.memStorRegName (GF := GF) by rw [Hrn1]; rfl]
    iapply rnSnapOnce_of_tok h85 _ γrn (srvRAddr s) bv.storage' γs Hrn7 $$ Hpkg Hrn [] Hsnone
    rw [Hrn1]; iexact Hminv
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  iNamedPrefix Hrn' "N"
  -- the lessor
  -- (the lease-expiry plan's X4) at the environment's grant flag and auth mode (`M.isOn = on`)
  ihave #Hlok : lessorOk ρ.rd.kv.lg M.isOn (lease.lessorIface lp) $$ []
  · icases HM with %HM'
    rw [HM'.1]
    iapply lessorOk_of_lessorInv h57 h58 h59 lp γl ρ.rd.kv.lg on
    iframe Hlexp Hlcfg Hlinv Hlspkg
  -- (R8) the lessor's and the auth store's apply contracts at the store's backend and the frozen
  -- hook (`snap_isApplyLessor`, `snap_isAuthStore`, as the snapshot walk's)
  ihave #HlinvM : lease.lessorInv lp (mvcc.api.mvccLeases γm) $$ []
  · rw [Hγl]; iexact Hlinv
  ihave #HllkO : lessorLookupOk lp $$ []
  · iunfold lessorLookupOk; iexact Hllk
  ihave #Hapl := snap_isApplyLessor h49 h50 h51 h52 h53 h54 h55 h56 h95 M alst astl lp bc.cl'
      ({ d with cm := true } : mvcc.KBReal) γm (mvcc.api.mvccW d.gx)
      (batchLockInv γA (metaTM d.γB d.P)) hook Hhknn HlP
    $$ [$Hpkg $Hlbe $Hlcfg $HllkO $HlinvM $HBs $Hhooks]
  ihave #Hast0 := snap_isAuthStore M alst astl lp bc.cl' RD ({ d with cm := true } : mvcc.KBReal)
      (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P)) hook Hhknn $$ [$HisAuth $HBs $Hhooks]
  ihave #Hast : apply.isAuthStore ast (fun _ => batchLockInv γA (metaTM d.γB d.P)) hook
      (srvBkTie ({ d with cm := true } : mvcc.KBReal)) RD M
      (srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be)) $$ []
  · rw [Hastl]; iexact Hast0
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
  -- (D19g (b)) what serving needs: the configuration fields, the watchable store as the KV, the
  -- progress interval's field, `lgMu`'s reader slots for request goroutines and the others'
  icases replicate_takeN _ 64 _ (by omega) $$ Hlgrs with ⟨Hlgs, Hlgrs⟩
  -- (D19i part 2) the storage version monitor's `lgMu` reader slot
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨HlgSV, Hlgrs⟩
  -- (audit B4a) `monitorDowngrade`'s `lgMu` reader slot, and the monitors' configuration fields
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨HlgMon, Hlgrs⟩
  -- (M2) one for the compactor's calls (`srvCompactR`)
  icases replicate_take1 _ _ (by omega) $$ Hlgrs with ⟨HlgC, -⟩
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
  -- (J8a-3, 2026-11-01) the configuration read-only but for the two fields `start` writes
  -- (`SnapshotCount`, `SnapshotCatchUpEntries`): the rest persisted, and the whole struct back
  -- read-only from those two once `start` has persisted them (`srvSnapRO`'s rebuild)
  ipersist NameS
  ipersist DiscoveryCfgS
  ipersist ClientURLsS
  ipersist PeerURLsS
  ipersist DataDirS
  ipersist DedicatedWALDirS
  ipersist MaxWALFilesS
  ipersist BackendBatchIntervalS
  ipersist BackendBatchLimitS
  ipersist BackendFreelistTypeS
  ipersist InitialPeerURLsMapS
  ipersist InitialClusterTokenS
  ipersist NewClusterS
  ipersist PeerTLSInfoS
  ipersist CORSS
  ipersist HostWhitelistS
  ipersist InitialElectionTickAdvanceS
  ipersist BootstrapTimeoutS
  ipersist AutoCompactionRetentionS
  ipersist AutoCompactionModeS
  ipersist CompactionBatchLimitS
  ipersist CompactionSleepIntervalS
  ipersist StrictReconfigCheckS
  ipersist AuthTokenS
  ipersist BcryptCostS
  ipersist TokenTTLS
  ipersist InitialCorruptCheckS
  ipersist CompactHashCheckTimeS
  ipersist PreVoteS
  ipersist SocketOptsS
  ipersist ForceNewClusterS
  ipersist LeaseCheckpointIntervalS
  ipersist EnableGRPCGatewayS
  ipersist WatchProgressNotifyIntervalS
  ipersist UnsafeNoFsyncS
  ipersist MemoryMlockS
  ipersist BootstrapDefragThresholdMegabytesS
  ipersist MaxLearnersS
  ipersist LocalAddressS
  ihave #HcfgRb : iprop(□ (∀ (sc scu : w64),
      srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc -∗
      srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu -∗
      srvCfgAddr s ↦□ ({ cfg with SnapshotCount' := sc, SnapshotCatchUpEntries' := scu } :
        go_etcd_io.etcd.server.v3.config.ServerConfig))) $$ []
  · iintro !> %sc %scu #Hsc #Hscu
    iapply typedPointsto_combine _ _ _ HCfgnn
    simp only [TypedPointsto.typedPointstoDef]
    rw [Hfgi]
    iframe #
  -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`srvSnapBoot`,
  -- `SnapRO.lean`): its persistent bundle, the snapshot-taken counter's authority (J8a-6: no stock
  -- of `lgMu`'s reader slots any more, the snapshots' `AddPeer`s borrowing from the transport's pool)
  ipersist DataDirS
  ipersist snapshotter
  ipersist beHooks
  obtain ⟨stp, Hstp, Hstpss⟩ := Hrn15
  ihave HsnapB : srvSnapBoot s cil
      (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF)
      ρ.rd γA $$ [Hγt Hopen Hpath]
  · iunfold srvSnapBoot
    iexists γt
    iframe Hγt
    isplitr [Hopen Hpath]
    · icases Hbh with ⟨%lgh, #Hbh'⟩
      ihave #Hfix' := Hfix
      iunfold rnFixed at Hfix'
      iNamed Hfix'
      iunfold srvSnapRO
      imodintro
      iexists cfg, bs.ss', bk.beHooks', lgh, stp, γd, bc.nodeID', alst, astl, lp, bc.cl', ps, dir, ({ d with cm := true } : mvcc.KBReal)
      simp only
      ihave #HszS := keySized_withCm d true $$ Hsz
      rw [← Hstp, ← Hastl, Hfgi]
      iframe LoggerS DataDirS ServerFeatureGateS Hfg QuotaBackendBytesS WarningApplyDurationS
      iframe snapshotter Hss beHooks Hbh' storageC memberID alarmStore authStore lessor cluster
      iframe HalS HalA HisAuth HauR HauSK Hlbe Hlcfg Hrc Hisc HszS
      isplitr
      · ipureintro
        refine ⟨trivial, Hlgnn, Hstpss, Hdisk.1, Hmmap, Hbuq, ?_, Hdirps.1, Hdisk.2.1, HbP,
          Hci0, HhP, HPwf, HPlim, HlP, ⟨HalB, HauB, HauUB, HauRB⟩, trivial, by omega⟩
        rw [HρRaft, Hid]; exact Hsloc
      isplitr
      · iExactEq Hsdir
        rw [Hγn.1, HρRaft]; rfl
      isplitr
      · iunfold lessorLookupOk; iexact Hllk
      isplitr
      · iexists _; iexact Hvcn
      isplitr
      · iunfold srvMembersDir; iexact Hmembers
      isplitr
      · iexact HlinvM
      isplitr
      · -- (the lease-expiry plan's X2) the lessor's mode at the lease mode `m`
        isplitr
        · first | itrivial | (ipureintro; rfl)
        · rw [Hγl, show (decide (ρ.rd.kv.lm = .mono)) = decide (m = .mono) by
            rw [lease.bootCfg_lm Hlbc]]
          iexact Hlmode
      isplitr
      · iframe kv HisKV
      -- (J8a-3) the configuration's rebuild
      iexact HcfgRb
    -- (D22 J1b) the backend's stop channels and the constructors' half of its open token, the
    -- alarm store's field; (2026-11-01) the KV's closer, the backend file's directory entry
    iunfold srvSnapRes
    iexists ({ d with cm := true } : mvcc.KBReal), alst, cfg.DataDir'
    ihave #HSCE : srvStopChans γA ({ d with cm := true } : mvcc.KBReal) $$ []
    · iunfold srvStopChans
      isplitr
      · iExactEq HB; rfl
      iExactEq HSC; rfl
    iframe Hopen alarmStore DataDirS Hpath
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact HSCE
    -- (R2b-3d) the backend's file at the backend path (`bootOk`'s)
    iexact Hbfile
  -- (S7b) the request path's `bemu` reader slots, at some current backend's ghost variable
  ihave Hbmr2 : srvBemuReader (GF := GF) s $$ [Hbmr2]
  · iunfold srvBemuReader; iexists γbe; iunfold srvBemuReaderAt; iexact Hbmr2
  ihave Hbms := replicate_mono _ (srvBemuReader (GF := GF) s) 64
    (by iintro H; iunfold srvBemuReader; iexists γbe; iunfold srvBemuReaderAt; iexact H) $$ Hbms
  ihave Hserve : srvServeBuilt s
      (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF)
      cfg 64 $$ [Hbmr2 Hlts Hlgs HRDs HrdServe Hbms]
  · unfold srvServeBuilt srvServeFacts srvServeCfg srvLeadTimeReader
    isplitr
    · isplitr
      · iexists ws
        iframe kv HisKV
        ipureintro; rfl
      · iframe MaxConcurrentStreamsS TracerOptionsS EnableDistributedTracingS MetricsS WarningUnaryRequestDurationS MaxTxnOpsS LoggerS QuotaBackendBytesS WatchProgressNotifyIntervalS
        try (ipureintro; exact Hmto)
    iframe Hbmr2 Hlts Hlgs HRDs Hbms
    iapply (mvccReaders_rep hRS γm 64) $$ HrdServe
  -- (D19i part 2) the storage version monitor's read token, with an open share
  -- (D19i part 2) the storage version monitor's backend access
  ihave HSV : srvSVRes s
      (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF)
      $$ [HbmSV HlgSV]
  · unfold srvSVRes srvBemuReaderAt
    iframe HbmSV HlgSV
  -- (D21 M5) the server is member `id` of the network: `RaftHandler`'s premise
  ihave #Hnm : srvNetMember γn s id ⟨t, c⟩ $$ []
  · iunfold srvNetMember
    isplitr
    · iexists γd; iexact Hprocok
    simp only
    iframe Htrf
    isplitr
    · ipureintro; exact Hcl
    iframe Hst
    ipureintro
    intro f hf hne
    rw [HcLm]
    refine ⟨?_, hne⟩
    rw [netRh_member, Hγn.2] at hf
    exact (Hdirps.1 f).1 hf
  ihave HtokP : srvTrTok γn ⟨t, c⟩ $$ [HtokP]
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
      (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF)
      64 $$ [HrdWatch]
  · unfold srvWatchReaders srvWatchBuilt
    iframe HrdWatch
    iexists ws
    iframe kv HisKV
    ipureintro; rfl
  -- (E3n) the construction's resource at the server's frozen hook, and (C1's A1) the token rights'
  -- empty authority
  ihave HABfi := authApplyResB_of_pre M astl srvAuthSt0 d (mvcc.api.mvccW d.gx)
      (batchLockInv γA (metaTM d.γB d.P)) RD hook $$ [HAres HRD]
  · iframe HB Hhook
    isplitl [HAres]
    · iExactEq HAres
      rfl
    isplitr
    · ipureintro; exact Hhknn
    -- (P6.2) the auth store's first reader ticket, the apply thread's (`Recover`'s at an install)
    iapply authRdM_of $$ HRD
  icases HABfi with ⟨HAresB, HFI⟩
  ihave HTR : srvTokRights (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF)
      (ciEff γA (⟨W64 0, W64 0, W64 0, false⟩ : ApplyState).k) $$ [HFI]
  · iapply srvTokRights_init
    iexact HFI
  -- (the auth plan's E2k) the auth store's resources for the apply thread
  ihave HAR : srvAuthApplyResB s
      (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF) srvAuthSt0 $$ [HAresB]
  · unfold srvAuthApplyResB
    iexists astl, ({ d with cm := true } : mvcc.KBReal), batchLockInv γA (metaTM d.γB d.P)
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    rw [← Hastl]
    iframe authStore
    isplitl [HAresB]
    · rw [authApplyResB_kb_congr _ _ _ d ({ d with cm := true } : mvcc.KBReal)
        _ _ _ rfl rfl rfl]
      iexact HAresB
    -- (E3l) the equation of the backend names: the write right lends the store's half on `d.be`
    isplitr
    · iapply rwLens_authBeOn
    -- (E3n) and so does the rest resource, at the same rest value
    iapply roLends_authBeOn
  -- (the auth plan's E3zb) the lessor finds no lease
  ihave #HLnil : iprop(□ (⌜on = true⌝ → srvLessorNil s)) $$ []
  · iintro !> %hon
    iunfold srvLessorNil
    iexists (lease.lessorIface lp)
    ihave #Hln := Hlnil $$ %hon
    iframe lessor Hln
  -- (authkv's Main) with auth on, the store's cost field; (C1's A4) and its `Authenticate` side
  ihave #HBF : iprop(□ (⌜on = true⌝ → srvAuthStoreOn s RD)) $$ []
  · iintro !> %hon
    icases HM with %HM
    ihave ⟨⟨%c, #Hc⟩, #Hau⟩ := Hbc $$ %(by rw [HM.1]; exact hon)
    iunfold srvAuthStoreOn
    iexists astl, c
    rw [← Hastl]
    iframe authStore Hc Hau
  -- (R2b-3d stage 5b, 2026-11-05) with auth off, the store's `Close` (`srvCleanupOwn`, for the stop)
  ihave #HCO : iprop(□ (⌜M.isOn = false⌝ → srvCleanupOwn s)) $$ []
  · iintro !> %hoff
    have hM : M = auth.AuthMode.off := by
      cases M <;> first | rfl | (simp [auth.AuthMode.isOn] at hoff)
    ihave #Hcl := HauC $$ %hM
    iunfold srvCleanupOwn
    iexists astl
    rw [← Hastl]
    iframe authStore Hcl
  -- (K7) the lease service's server facts: the peers' round tripper, the lessor's reader side
  ipersist peerRt
  ihave #HpeerRt : srvPeerRt s $$ []
  · iunfold srvPeerRt
    iexists _
    iframe peerRt
    ipureintro; exact Hprt
  ihave #HlessRd : srvLessorRd s (mvcc.api.mvccLeases γm) $$ []
  · iunfold srvLessorRd
    iexists lp
    iframe lessor
    rw [Hγl]; iexact Hlinv
  ihave #HlPool' : lease.lessorRdPool (GF := GF) (mvcc.api.mvccLeases γm) $$ []
  · rw [Hγl]; iexact HlPool
  -- (2026-11-04, the lease-expiry plan's Part C) the lease subsystem's slot
  ihave #HLsrv : lease.srvInv on s (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF) m $$ [HLnil HpeerRt HlessRd HlPool']
  · iapply lease.srvInv_intro
    iframe HLnil HpeerRt HlessRd HlPool'
    simp only
    rw [Hγl]
    iframe Hlmode Hl0
  -- (E3 (c) stage 2) the lease-TTL row's raft part (`leaseTTLRowR`): the member id, the node
  -- `StartNode` made (`nodeStartedFresh`), every committed configuration the boot's
  -- (`srv_confAt_simple`)
  ihave #HttlR : leaseTTLRowR s γ.vs $$ []
  · iunfold leaseTTLRowR
    iexists id, γrn.nl, γ, ctxs
    isplitr
    · ipureintro; rw [Hrvs]; exact Hrid ▸ Hrmem
    isplitr
    · rw [← Hid]; iexact memberID
    isplitr
    · iexact HNodeC
    isplitr
    · rw [Hrvs, ← Hrid]; iexact Hsfresh
    iintro !> %l %k #Hl %hk
    ihave #Hsrl0 : srvRaftLogInv (GF := GF) (⟨γ, [], W64 0⟩ : ServerRaftNames) $$ []
    · rw [← HρRaft]; iexact Hsrl
    imod srv_confAt_simple (GF := GF) ⟨γ, [], W64 0⟩ l k hk ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) $$ [$Hsrl0 $Hl] with #Hc
    imodintro
    irevert Hc
    simp only [SrvRaft.cfg]
    iintro #Hc
    iexact Hc
  -- (2026-11-04, R2b-3d) what the stop needs of the construction (the stop's slot, `srvStop.keep`): the raft loop's
  -- stop claim, the registry's authority, the lessor's stop right, the WAL's directory
  -- (2026-11-05, R2b-3d gap 4) the apply thread's reader of the store (`apply.kvOwn`'s, below), and
  -- the rest of the store's readers kept for the stop (until then dropped)
  -- the compactor's reader token: kept for the stop when there is no compactor, else the
  -- compactor's (R2c-2: a compactor only in compaction mode)
  icases newServer_cmp_peek $$ Hcpt with ⟨%Hcpc, Hcpt⟩
  ihave ⟨HcpK, HwrC⟩ : iprop(((⌜cpv = GoInterface.nil⌝ ∗ mvcc.api.mvccReaders γm 1) ∨
      ⌜cpv ≠ GoInterface.nil ∧ E₀.cmp = true⌝) ∗ (⌜cpv = GoInterface.nil⌝ ∨ mvcc.api.mvccReaders γm 1))
      $$ [HrdC]
  · by_cases hc : cpv = GoInterface.nil
    · isplitl [HrdC]
      · ileft; iframe HrdC; ipureintro; exact hc
      · ileft; ipureintro; exact hc
    · isplitr
      · iright; ipureintro
        exact ⟨hc, by rw [Hcmp0]; exact Hcpc.resolve_left hc⟩
      · iright; iexact HrdC
  ihave HStopK : srvStop.keep (GF := GF) s cfg
      (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF)
      γrn γk $$ [Hrsc Hrauth Hlstop HrdKeep HcpK]
  · iapply srvStop.keep_intro
    iframe Hrsc
    isplitr
    · iunfold srvTrKeyOf; iexists _; iframe Hkx; ipureintro; rfl
    isplitl [Hlstop]
    · iexists lp
      iframe lessor Hlstop
    isplitr
    · iintro !> %hoff
      iapply HCO
      ipureintro; exact hoff
    ihave #HfixS := Hfix
    iunfold rnFixed at HfixS
    iNamed HfixS
    isplitl [HrdKeep]
    · iexact HrdKeep
    isplitl [HcpK]
    · iexists cpv
      iframe compactor HcpK
    isplitl [Hrauth]
    · rw [show γrn.node.reg = MemStorReg.memStorRegName (GF := GF) by rw [Hrn1]; rfl]
      iexists _
      iexact Hrauth
    iframe DataDirS DedicatedWALDirS
    iexists rvr.raftNodeConfig'.storage'
    iframe storageC
    ipureintro
    rw [Hrnwal]; exact HwDir
  -- (revoke-open, 2026-11-06) the revocation's inner pool: `srvRevokePoolN` of `leadTimeMu`'s rest
  -- and of the auth store's stock of tickets (`authRdN`'s `2 ^ 28`), paired, at level 1
  icases replicate_takeN _ srvRevokePoolN _ (by
      unfold srvRevokePoolN backend.rdPoolN; rw [sync.rwmutex.actualMaxReaders_unseal]; decide)
    $$ HltRest with ⟨HltI, -⟩
  icases replicate_takeN _ srvRevokePoolN _ (by unfold srvRevokePoolN backend.rdPoolN; omega)
    $$ HRDstock with ⟨HRDI, -⟩
  -- (2026-11-06) the lists are paired at their elements' own forms (`leadTimeMu`'s slot, not
  -- `srvLeadTimeReader`): no tactic rewrites the goal, no bare `iframe` compares the lists (a
  -- mismatched `[∗list]` unfolds the `List.replicate`; this step reached 80 GB before)
  ihave HIp := replicate_sep (sync.ownRWMutex (srvLeadTimeMuAddr s) (leadTimeP s)) RD
    srvRevokePoolN $$ [HltI HRDI]
  · isplitl [HltI]
    · iexact HltI
    · iexact HRDI
  imod threadPool.initL srvRevokeInnerN 1
      iprop(sync.ownRWMutex (srvLeadTimeMuAddr s) (leadTimeP s) ∗ RD) _ srvRevokePoolN
      (by unfold srvRevokePoolN backend.rdPoolN; omega) $$ HIp with ⟨%γI, #HIp⟩
  -- (R2d'a A10 item 5) `Hwpend`'s token (`srvWinPend`, free at a first start)
  imod (token_alloc (GF := GF)) with ⟨%γwp, Hwpt⟩
  imodintro
  wp_auto
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iframe Htok
  iexists γA, cil, metaTM d.γB d.P,
    (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF),
    γrn, (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be : GoInterface), γk,
    (⟨t, c⟩ : SrvTr GF)
  iframe Hgap Hserve HSV HMon Hrc Hnm HWR HtokP HServe
  iframe HLsrv HttlR HBF ClientCertAuthEnabledS HStopK
  isplitr
  · icases HM with %HM; ipureintro; exact ⟨hγs, HM.1, HM.2⟩
  isplitr
  · unfold srvWatchBuilt
    iexists ws
    iframe kv HisKV
    ipureintro; rfl
  -- (D22 S-g, S-j2) the KV's closer and the backend file's directory entry: in the built part
  -- since D22 J1b (`srvSnapBoot`)
  -- (2026-11-02, branch `snap-window`) the server's backend with its hooks (`srvBeHooked`):
  -- `bootOk`'s hooks and `hooksAt`, the backend at the protocol's batch-lock resource
  ihave #HbeHk : srvBeHooked s γA cil (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF) $$ []
  · icases Hbh with ⟨%lgh0, #Hbh0⟩
    iunfold srvBeHooked
    iexists ({ d with cm := true } : mvcc.KBReal), bk.beHooks', lgh0, d.gx
    iframe Hbh0 HhkAt beHooks
    isplitr
    · ipureintro; exact ⟨rfl, Hci0, HhP, rfl⟩
    iExactEq HB; rfl
  -- (revoke-open, 2026-11-06) the revocation's built part: the inner pool from `leadTimeMu`'s rest
  -- and the auth store's stock of tickets (`authRdN`'s `2 ^ 28`), `raftPool`, the store's pointer
  ihave #Hrvkb : srvRevokeBuilt s (({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF) $$ []
  · iapply srvRevokeBuilt_intro s _ astl
    isplitr
    · iapply srvRevokeInnerPool_intro s _ γI
      iexact HIp
    iframe HrPool
    rw [← Hastl]
    iframe authStore
    ipureintro; unfold backend.rdPoolN; omega
  unfold srvBuiltG
  iframe HsCI Hloop Happly Hrdone Hcci Hwci Hai Hti Hcmi Hrn Hrvkb
  isplitr
  · -- `#Hfb`
    iexists ⟨cfg.Logger', GoInterface.nil, lease.lessorIface lp, #hook, fcn, alst, bc.cl',
      cfg.QuotaBackendBytes', «$v2_ptr», bc.nodeID', cfg.ElectionTicks', cfg.TickMs'⟩
    unfold srvFieldsBuiltNA srvLeadInv
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro; exact ⟨⟨rfl, rfl, Hhknn⟩, rfl, rfl, d.γB, _, rfl, rfl,
      ({ d with cm := true } : mvcc.KBReal), alst, astl, lp, rfl, rfl, rfl⟩
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
          ({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) =
          srvFloorFact E₀ := by
        rfl
      rw [hff]; iexact Hgen
    isplitr
    · iunfold srvRaftNode
      iexists rnNodeIface γrn
      iframe Hnodef Hprop
    ipureintro; exact ⟨HCfgnn, Hmrb⟩
  isplitr
  · -- `#Hrdb`
    iexists ⟨null, GoInterface.nil, lease.lessorIface lp, ast, cfg.Logger', cfg.WarningApplyDuration',
      GoInterface.nil, null, fcn, null⟩
    unfold srvReadBuiltNK
    iframe firstCommitInTerm Hast Hapl Hti WarningApplyDurationS lessor authStore lg
    isplitr
    · ipureintro; exact Hlgnn
    iexists [[], []]
    iframe Hlb0
    ipureintro; exact ⟨by simp, mvcc.LogPutsLe.empties _⟩
  isplitr
  · -- `#Hrunb`
    iexists ⟨errc, null, null, func.nil, cpv, sstats, null⟩
    unfold srvRunBuilt
    iframe compactor errorc Hltg stats Herrb Hcpok
  isplitl [Hcpt HltC HlgC HRDC HwrC]
  · -- `Hcrun` (M2, S4): the compactor off, nothing to run; on, its run token and the run's
    -- precondition from the views `start` builds (`compactorRun`)
    iexists cpv
    iframe compactor
    iunfold compactorRun
    icases Hcpt with (%Hn | ⟨%Hcm, %Hcrm, %T, %γf, #Hcpo, HT⟩)
    · ileft; ipureintro; exact Hn
    -- (2026-11-05) a compactor, so its reader was not kept for the stop
    icases HwrC with (%Hnil | HwrC)
    · iexfalso
      iunfold v3compactor.compactorOk at Hcpo
      icases Hcpo with ⟨%ci, %Hci, -⟩
      rw [Hnil] at Hci; cases Hci
    iright
    subst Hcm
    -- (K1) auth off in compaction mode; the mode's permit carried from where the compactor is built
    have Hon : on = false := Hcon rfl
    isplitr
    · icases HM with %HM; ipureintro; show M.isOn = false; rw [HM.1, Hon]
    iexists T, _
    iframe Hcpo HT
    iintro %ρ' ⟨#Hpk', #Hreq', #Hrd', #Hcred'⟩
    unfold v3compactor.runPre
    simp only
    imodintro
    isplitr
    · ihave #Hrg := revGetterOk_server Hp Hr hsh s ({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) ρ'.rd _ $$ [$Hmvpkg $kv $Hrd']
      iExactEq Hrg; rfl
    isplitr
    · ihave #Hcb := compactableOk_server_mode (hCmpS rfl) Hp Hr s ({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) ρ' cfg.AutoCompactionMode'
          (sint.Z cfg.AutoCompactionRetention') γf Hcmp0 Hcrm
        $$ [$Hpk' $Hreq' $Hrd' $Hcred']
      iExactEq Hcb; rfl
    isplitl [HltC HlgC HRDC HwrC]
    · unfold srvCompactR srvLeadTimeReader
      iframe HltC HlgC HRDC HwrC
    imodintro
    iunfold srvRevLb
    iexists [[], []]
    iframe Hlb0
    isplitr
    · imodintro; iexact Hnx0
    ipureintro; simp
  isplitr
  · -- `#Hsab`: `msgSnapC`, a bag of raft's `MsgSnap`s (2026-10-30, the repair: snapshots allowed)
    -- (2026-10-31, S1) the raft node's bag and the started transport
    unfold srvApplyAllBuilt
    iexists _
    iframe NHmsc Hinfl
    isplitr
    · iexists γrn
      iframe NHmsci
      isplitr
      · ipureintro; simp [Hrn1, HρRaft]
      have hidr : γrn.id = id := by rw [Hrn5, Hrid]
      rw [hidr, ← Hid]; iexact memberID
    isplitr
    · iexists (transportIface t), γn, id, srvTrKey γn γk, iprop(False)
      iframe Htrf Htrall
      ipureintro; rw [Hγn.1, ← hργ]
    ipureintro; exact ⟨Hc0, Hlog0⟩
  isplitr
  · -- `#Hkvi`
    unfold Perennial.named
    cases on
    · simp only [srvKVInvsM, srvKVInvs, kvInvM, kvCertInvM]
      iframe Hkci Hsrl Hkvinv
      isplitr
      · iexact HkvSG
      ipureintro
      refine ⟨⟨Hkcmp.trans Hcmp0.symm, ?_, ⟨fun _ => inferInstance, fun _ => inferInstance,
        fun _ => inferInstance, fun _ => inferInstance⟩, ?_⟩, ?_, ?_⟩ <;> first | exact True.intro | rfl
    · simp only [srvKVInvsM, srvKVInvsOn, kvInvM, kvCertInvM]
      isplit
      · iframe Hkci Hsrl Hkvinv Htie
        isplitr
        · iexact HkvSG
        ipureintro
        -- (#7-on) auth on, the compaction mode off (`specG`'s `cmp = true → on = false`)
        -- (the lease-grant merge) and a cluster that grants no lease (`specG`'s `on → lg = false`)
        have hcf : cmp = false := by
          cases hc : cmp
          · rfl
          · exact absurd (Hcon hc) (by decide)
        refine ⟨⟨⟨fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
          fun _ => inferInstance⟩, ?_⟩, ?_, Hkcmp.trans ?_, Hlgon rfl⟩
        all_goals first | exact True.intro | rfl | exact hcf
      · iapply srvUberOn_of_kit hKit
        iPkgInit
  isplitr
  · ipureintro
    refine ⟨?_, rfl, ⟨Int.le_refl _, Hrn6, rfl⟩, Hrna0⟩
    unfold srvErM
    simp only
    exact (srvCM_agree on ρ _ E₀ (W64 0) (W64 0) (bootKVOf on) hγs).symm
  isplitl [Hwpt]
  · -- (R2d'a A10 item 5) at a first start `Hwpend` is free (`srvWinPend_first`)
    iapply srvWinPend_first _ _ _ Hrna0 γwp
    iexact Hwpt
  isplitl [Hrunh]
  · iunfold named; iExactEq Hrunh; rfl
  isplitl [Hwth]
  · iexact Hwth
  isplitl [Hwtl]
  · iexact Hwtl
  isplitr
  · ipureintro; exact Hdisk
  isplitr
  · ipureintro; exact Hslg
  isplitr
  · ipureintro; rfl
  isplitr
  · -- (J8b) the member id, the raft node's (`srvProcOk`'s)
    have hidr : γrn.id = id := by rw [Hrn5, Hrid]
    rw [hidr, ← Hid]; iexact memberID
  isplitr
  · -- (2026-11-02, the cluster-rows stage) the member id, a voter (`srvDynLog`'s)
    ipureintro
    have hidr : γrn.id = id := by rw [Hrn5, Hrid]
    have hργ' : ρ.rd.raft.raft = γ := by rw [HρRaft]
    rw [hidr]
    try rw [hργ']
    unfold SrvRaft.cfg
    rw [Hrvs, GMap.elem_of_list_to_set, ← Hrid]
    exact Hrmem
  isplitr
  · -- (J8b) `bootOk`'s meta reads, by name
    unfold srvMetaSnap; iexact HmetaSnap
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
  · iexists _; iexact SnapshotCatchUpEntriesS
  isplitl [wg]
  · iexact wg
  isplitl [wgMu]
  · iexact wgMu
  isplitl [Hcmown]
  · iexists _; iexact Hcmown
  isplitl [Hnot]
  · iexact Hnot
  isplitl [Hthr Happ Hown Hlr5 Hbmr HrdApp beA HγbA HbkP HrtA Hrev HAR Hrdat Haown Hkhi2 forceDiskSnapshot Hrbo Hmem HalOn HauthOn HleOn HclBe Htlive HltS HlEv HTR]
  · -- `Happ` (E3c: the mode-`on` row, the auth resource at the store's start state)
    iapply applyBuiltNAM_of_On
    unfold applyBuiltNAOn srvBemuReaderAt
    iexists ⟨W64 0, W64 0, W64 0, false⟩, W64 0, W64 0, false
    iframe Hthr Happ Hlr5 Hbmr HrdApp Haown forceDiskSnapshot HTR
    isplitr
    · ipureintro
      have hm0 := Hci.2
      refine ⟨⟨rfl, ?_⟩, ?_⟩ <;> simp [ciEff, hm0]
    isplitl [Hown]
    · unfold applyBackend
      iframe Hown Hmeta
    -- (2026-11-02, the backend-auth-split stage) with the backend's reader pool (`newPost_pool`'s)
    isplitl [beA HγbA HbkP HrtA]
    · iunfold srvBeOwn; iexists ({ d with cm := true } : mvcc.KBReal); iframe beA HγbA
      isplitr
      · ipureintro; rfl
      isplitr
      · iunfold srvBeRO
        iexists d.gx, batchLockInv γA (metaTM d.γB d.P); iexact HBs
      isplitl [HbkP]
      · iExactEq HbkP; rfl
      iexact HrtA
    isplitl [Hrev]
    · unfold revAuth
      iexists ∅
      iframe Hrev
      ipureintro; intro k hk; simp at hk
    isplitl [HAR]
    · iexact HAR
    -- (2026-11-04, the lease-expiry plan's step 2) the range deleter, `mvcc.New`'s
    isplitl [Hrdat]
    · iExactEq Hrdat; simp [Hγl]
    isplitr
    · simp only [bootKVOf]; rw [← Hlog0]; iexact Hal0
    isplitr [Hrbo Hmem HalOn HauthOn HleOn HclBe Htlive HltS HlEv]
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
        ipureintro; simp [bootKVOf, Hch0, crevOf, kvCrevOf]
      ipureintro; exact ⟨Hc0, by simp [ReqNames.raft, HρRaft]⟩
    · -- (D22, 2026-10-23) the rest buckets and the members at the start: the boot state; (the
      -- lease-grant stage, 2.13) the apply thread's half of the live set at `[]`, and in a cluster
      -- that grants leases the lessor's guard and mode (`srvGrantable`)
      have hpre : ρ.rd.raft.pre = [] := by simp [HρRaft]
      isplitl [Hrbo Hmem HalOn HauthOn HleOn HclBe HltS HlEv]
      · iapply srvRest_init _ _ hpre
        rw [restModel_nil]
        dsimp only
        isplitl [Hrbo Hmem HalOn HauthOn HleOn HclBe]
        · unfold srvRestOwnH srvRestOwn restBoot srvObjsOn
          have hb0 : ρ.rd.raft.raft.boot = γ.boot := by rw [HρRaft]
          rw [hb0]
          -- (2026-11-02, the backend-auth-split stage) the cluster's buckets idle, the others a part
          -- (P5) of the mode's buckets: the auth ones the realization's in `on`
          icases rbOwnIn_kit_rest M d.γB _ $$ Hrbo with ⟨Hrbc, Hrbn⟩
          isplitl [Hrbc Hrbn Hmem]
          · iframe Hrbc Hrbn Hmem
            ipureintro; exact ⟨memIdOk_memBoot _, restPresent_restBoot _⟩
          iframe HalOn HauthOn HleOn HclBe
        isplitl [HltS]
        · iunfold apply.ltHalf
          simp only [apply.AEnv.lg_eq, KVNames.lg_fold]
          cases ρ.rd.kv.lg
          · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
          · simp only [↓reduceIte]; iexact HltS
        isplitr [HlEv]
        rotate_left
        · iunfold apply.everOwn
          simp only [apply.AEnv.lg_eq, KVNames.lg_fold]
          cases ρ.rd.kv.lg
          · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
          · simp only [↓reduceIte]; rw [Hγl]; iexact HlEv
        unfold srvGrantIf srvGrantable
        dsimp only
        simp only [apply.AEnv.lg_eq, KVNames.lg_fold]
        by_cases hlg : ρ.rd.kv.lg = true
        · have hon : on = false := by
            cases on
            · rfl
            · rw [Hlgon rfl] at hlg; cases hlg
          simp only [hlg, ↓reduceIte]
          rw [Hγl]
          isplitl []
          · iintro !> %lid
            iunfold lease.leaseGranted
            iexists _
            iframe Hlgd
            iintro !>
            iunfold srvGrantGuard
            ipureintro; exact ⟨rfl, hon⟩
          rw [show (decide (ρ.rd.kv.lm = .mono)) = decide (m = .mono) by
            rw [lease.bootCfg_lm Hlbc]]
          iexact Hlmode
        · simp only [hlg, Bool.false_eq_true, ↓reduceIte]; itrivial
      -- (D43 M5e) the apply thread's membership resource: the frozen transport's stop token
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
      rw [hργ]
      iframe Hrc
      isplitl [Htlive]
      · iexists γn, c, ps
        rw [Hγn.2]
        iframe Htlive
        isplitr
        · ipureintro; rw [Hcl, Hid]
        isplitr
        · iunfold srvMembersDir; iexact Hmembers
        ipureintro
        refine ⟨Hdirok, Hdirps.1, fun f hf => ?_⟩
        try rw [hργ] at hf
        unfold SrvRaft.cfg at hf
        rw [Hrvs, GMap.elem_of_list_to_set] at hf
        exact (Hdirps.1 f).2 hf
      ipureintro
      refine ⟨⟨fun f hf hne => ?_, ?_⟩, ?_⟩
      · apply Hcov f _ (by rw [Hid] at hne; exact hne)
        rw [netRh_member, Hγn.2]
        rw [hργ] at hf
        unfold SrvRaft.cfg at hf
        rw [Hrvs, GMap.elem_of_list_to_set] at hf
        exact (Hdirps.1 f).2 hf
      · exact srvMemOk_boot _ _ ps (by rw [HρRaft]) (by rw [hργ]; unfold SrvRaft.cfg; rw [Hrvs])
          Hrnodup (by have := Hdirps.2; omega) (by rw [hργ]; exact Hrbok)
      · unfold SrvRaft.cfg
        rw [Hrvs, GMap.elem_of_list_to_set, Hid, ← Hrid]
        exact Hrmem
  iframe Hlr3 Hlr4
  isplitl [Hfcr]
  · iexists fcn
    iframe firstCommitInTerm Hfcr
  isplitr
  · -- `#Hkv`: the watchable store, the store's handle (`mvcc.New`)
    iexists _
    iframe kv HisKV
    ipureintro; rfl
  -- `HWB`: the stores' write budget (`boot_storage`'s)
  isplitl [HWreg]
  · iunfold srvWTBudget; iexists γp
    iframe HWA0 HWreg
    iapply HWBp; ipureintro; rfl
  -- the lifetime premises (D17): the id supply from the time-receipt bound (D19b), the thread
  -- bound; `ClusterVersion()` from the cluster's `Version` contract
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
  · ipureintro; (try unfold backend.rdPoolN); omega
  -- `Hua`: the uber-applier (D14i): its options' contracts, its chain, the apply thread's KV
  have hm0 : γA.m0.1 = W64 0 := by rw [Hci.2]
  have hLoaded : ∀ st : ApplyState, stLoaded γA st = st := by
    intro st; unfold stLoaded; split
    · rename_i h; cases st; simp only at h; subst h; simp [hm0]
    · rfl
  -- (R8) the store's builders at the environment (`envAus`): `kvAusG`'s at the store invariant,
  -- the writer's floor (`writer_floor`)
  ihave #Haus : apply.envAus ({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) $$ []
  · ihave #Hk := srvApi.kvAusG (srvApi.kvNx ρ.rd on) (kvCpOk ρ.rd.kv) Hp Hr _ γm E₀.γs $$ HkvSG
    icases Hk with ⟨#HB1, #HR1, -, #HE1, #HC1, -, -, #HF1⟩
    iunfold apply.envAus
    isplitr
    · imodintro; iExactEq HB1; rfl
    isplitr
    · imodintro; iExactEq HR1; rfl
    isplitr
    · imodintro; iExactEq HE1; rfl
    isplitr
    · imodintro; iExactEq HC1; rfl
    isplitr
    · -- (the parent's change) the writer's witness under `□`
      iintro !> %log %c Hw
      imod HF1 $$ %log %c Hw with ⟨Hw, #Hlb, #Hnx, Hrc, %Hre⟩
      imodintro
      iframe Hw Hlb Hrc
      isplitr
      · imodintro; iexact Hnx
      ipureintro; exact Hre
    iintro !> %log %c %F Hw HF
    iapply (srvApi.writer_floor (srvApi.kvNx ρ.rd on) (kvCpOk ρ.rd.kv) Hp _ γm E₀.γs log c F) $$ HkvSG Hw HF
  ihave #Hbo : apply.backendOptsOk ({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) uopts $$ []
  · obtain ⟨Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7, Hu8, Hu9, Hu10, Hu11, Hu12⟩ := Huopts
    iunfold apply.backendOptsOk
    simp only
    rw [Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7, Hu11, Hu12]
    isplitr
    · ipureintro; exact Hlgnn
    isplitr
    · iunfold apply.isApplyKV; iexact HisKV
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Haus
    isplitr
    · iexact Hapl
    isplitr
    · iexact Hast
    isplitr
    · iapply snap_isAlarmStore alst astl lp bc.cl' ({ d with cm := true } : mvcc.KBReal)
        (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P)) hook Hhknn
      iframe HalA HBs Hhooks
    isplitr
    · iapply snap_isCluster M alst astl lp bc.cl' ({ d with cm := true } : mvcc.KBReal)
        (mvcc.api.mvccW d.gx) (batchLockInv γA (metaTM d.γB d.P)) hook Hhknn
      iframe Hisc HBs Hhooks
      iexists _; iexact Hvcn
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
      iintro !> %C %x %HC
      obtain ⟨cst, cb, hC, hcp, -, hx⟩ := HC
      subst hC hx
      iintro %Φ' !> Hpre HΦ'
      iapply (wp_wand (Φ := fun w => iprop((
          iprop(applyThread γA cst ∗ applyBackend γA cil cb) -∗ Φ' #(ciEff γA cst.k)) ∗
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
  ihave Hul := Hulate $$ %(({ kv := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws, γ := γm, γs := E₀.γs, Nx := srvApi.kvNx ρ.rd on, Pk := fun _ => batchLockInv γA (metaTM d.γB d.P), f := hook, RD := RD, γrev := E₀.γrev, authMode := M, FS := srvFS s, ciC := srvCiC γA cil, RO := srvRestOwnH M d.γB bc.cl' (srvObjsOn alst astl lp bc.cl' d.be), RW := srvRestRWH d.γB (srvObjsOn alst astl lp bc.cl' d.be), γbe := γbe, Cp := kvCpOk ρ.rd.kv, BkTie := srvBkTie ({ d with cm := true } : mvcc.KBReal), cmp := E₀.cmp, cret := ρ.rd.kv.cret, lm := ρ.rd.kv.lm, γlt := γlt } : apply.AEnv GF) : apply.AEnv GF) Hbo
  icases Hul with ⟨#Hui, %ns, %cr, %Hz, Huo⟩
  obtain ⟨hns, hcr⟩ := Hz trivial
  subst hns hcr
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
    iframe HstL
    iexact HbBk
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
    simp only [apply.AEnv.authOn, HM'.1]
  -- (M2's apply side, A1) the compaction resources at `-1`: the right (`True` off) and the
  -- write-back supply (`True` off; on, the stock's)
  isplitr [Hopn Hcr0]; rotate_left
  · iunfold apply.cmpOwn
    iframe Hopn Hcr0
  iunfold apply.kvOwn
  isplitl [Hw0]
  · iexists _; iexact Hw0
  isplitl [HmB]
  · iunfold apply.kvBk
    iexists ({ d with cm := true } : mvcc.KBReal)
    iframe HmB
    isplitr
    · rw [mvcc.api.etcdStorage_hookIs]; iexact Hhooks
    iunfold srvBkTie; ipureintro; rfl
  iframe HRD2
  iunfold apply.leasesLive
  iexists []
  isplitr
  · iunfold txn.leasesKnown; simp [mvcc.stateAfter, txn.leasesOk]
    iintro !> %l %h
    obtain ⟨a, ha, -⟩ := h
    simp [mvcc.applyChanges] at ha
  iunfold lease.lessorUser
  simp only
  rw [Hγl]
  iframe Hlrd2 Hlrvk
  -- the initial state has no key: its item map is the lessor's, empty
  have h0 : (∅ : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) =
      mvcc.leaseItemsOf (mvcc.stateAfter ([[], []] : mvcc.Log)) := GMap.ext fun _ => rfl
  isplitl [Hlown]
  · iapply (lease.leaseOwn_eq h0) $$ Hlown
  iunfold apply.ltHalf
  simp only [apply.AEnv.lg_eq, KVNames.lg_fold]
  cases ρ.rd.kv.lg
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]; iexact Hlt1

/-- **`NewServer` with auth on or off** (`NewServer.specM`), the compaction mode off. -/
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
    -- (2026-10-27) the node API's node specs, at the cluster's storage model
    (h9 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Ready.spec (GF := GF) (hG := hG))
    (h10 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Advance.spec (GF := GF) (hG := hG))
    -- (2026-10-30, the repair) `node.Stop` (until then `node.Advance.dynamicSpec`)
    (h10d : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Stop.spec (GF := GF) (hG := hG))
    (h11 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Tick.spec (GF := GF) (hG := hG))
    (h12 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReadIndex.spec (GF := GF) (hG := hG))
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
    -- (step 6 of the auth-mode merge) what the uber-applier's contracts with auth on are built from
    (hKit : uberKitM (GF := GF) (hG := hG) on)
    (h26 : mvcc.api.New.spec (GF := GF) (hG := hG))
    -- (R6, 2026-11-07, the `lean` merge) mvcc's API laws the boot uses (the store over its
    -- storage, `BootStore.boot_storage`; the store invariant, `bootStore_holds`; the readers'
    -- census of the error paths, `stop_census`; the compactor's revision getter)
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hfresh : mvcc.api.mvccImage_fresh.law (GF := GF))
    (hopen : mvcc.api.etcdStorage_open.law (GF := GF))
    (hrest : mvcc.api.backendRest_open.law (GF := GF))
    (hRS : mvcc.api.mvccReaders_split.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (hSR : mvcc.api.mvccStorageFor_rest.law (GF := GF))
    (h27 : newCorruptionChecker.spec (GF := GF) (hG := hG))
    (h28 : mvcc.api.watchableStore.HashStorage.spec (GF := GF) (hG := hG))
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
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (h42 : mvcc.api.watchableStore.Close.spec (GF := GF) (hG := hG))
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
    (h78 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Propose.spec (GF := GF) (hG := hG))
    (h79 : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (h80 : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (h81 : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (h82 : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (h83 : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (h84 : EtcdServer.ClusterVersion.spec (GF := GF) (hG := hG))
    (h85 : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (h86 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ApplyConfChange.spec (GF := GF) (hG := hG))
    -- (2026-10-30, the repair) the fresh `MemoryStorage`'s methods `StartNode`'s `bootStorage` runs
    -- (`srvMem_bootStorage`; until then `node.ApplyConfChange.dynamicSpec`)
    (h86d : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (h86e : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (h86f : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (h86g : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (h86h : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    -- (D21 M2) the inbound path: raft's `Step` and reports, the server's `Process` and co.
    (h87 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Step.spec (GF := GF) (hG := hG))
    (h88 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h89 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (h90 : EtcdServer.Process.spec (GF := GF) (hG := hG))
    (h91 : EtcdServer.IsIDRemoved.spec (GF := GF) (hG := hG))
    (h92 : EtcdServer.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h93 : EtcdServer.ReportSnapshot.spec (GF := GF) (hG := hG))
    -- (leases T3, 2026-10-25) the backend's delete, for the lessor's in the store's contract
    (h94 : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    -- (the lease-revoke plan, 2026-10-31) the lessor's `Revoke`, for `isApplyLessor`'s clause
    (h95 : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    -- (2026-11-01, J8a-5) the alarm store's `Get` with no alarm, for the uber-applier's construction
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    -- (R-D1, 2026-11-04) the error paths' `b.Close()` (until then `bootOk`'s `#Hclose`)
    (hBSC : bootstrappedServer.Close.spec (GF := GF) (hG := hG)) :
    NewServer.specM (GF := GF) (hG := hG) on :=
  -- `specG` at `cmp = false`: the compaction mode's specs are not asked for
  NewServer.wp_proofG on false h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h10d h11 h12 h13 h14 h15 h16 h17 h18
    h19 h20 h21 h22 h23 h24 hTP hKit h26 Hp Hr hsh hfresh hopen hrest hRS hCR hSR h27 h28 h29 h31 h32 h33 h34 h35 h36 h37 h38 h39 h41 hPeerStop hRemoteStop h42 h46
    h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70
    h71 h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83 h84 h85 h86 h86d h86e h86f h86g h86h h87 h88
    h89 h90 h91 h92 h93 h94 h95 hAG hBSC
    (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)

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
    -- (2026-10-27) the node API's node specs, at the cluster's storage model
    (h9 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Ready.spec (GF := GF) (hG := hG))
    (h10 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Advance.spec (GF := GF) (hG := hG))
    -- (2026-10-30, the repair) `node.Stop` (until then `node.Advance.dynamicSpec`)
    (h10d : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Stop.spec (GF := GF) (hG := hG))
    (h11 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Tick.spec (GF := GF) (hG := hG))
    (h12 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReadIndex.spec (GF := GF) (hG := hG))
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
    (h26 : mvcc.api.New.spec (GF := GF) (hG := hG))
    -- (R6, 2026-11-07, the `lean` merge) mvcc's API laws the boot uses (the store over its
    -- storage, `BootStore.boot_storage`; the store invariant, `bootStore_holds`; the readers'
    -- census of the error paths, `stop_census`; the compactor's revision getter)
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hfresh : mvcc.api.mvccImage_fresh.law (GF := GF))
    (hopen : mvcc.api.etcdStorage_open.law (GF := GF))
    (hrest : mvcc.api.backendRest_open.law (GF := GF))
    (hRS : mvcc.api.mvccReaders_split.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (hSR : mvcc.api.mvccStorageFor_rest.law (GF := GF))
    (h27 : newCorruptionChecker.spec (GF := GF) (hG := hG))
    (h28 : mvcc.api.watchableStore.HashStorage.spec (GF := GF) (hG := hG))
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
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (h42 : mvcc.api.watchableStore.Close.spec (GF := GF) (hG := hG))
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
    (h78 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Propose.spec (GF := GF) (hG := hG))
    (h79 : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (h80 : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (h81 : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (h82 : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (h83 : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (h84 : EtcdServer.ClusterVersion.spec (GF := GF) (hG := hG))
    (h85 : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (h86 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ApplyConfChange.spec (GF := GF) (hG := hG))
    -- (2026-10-30, the repair) the fresh `MemoryStorage`'s methods `StartNode`'s `bootStorage` runs
    -- (`srvMem_bootStorage`; until then `node.ApplyConfChange.dynamicSpec`)
    (h86d : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (h86e : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (h86f : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (h86g : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (h86h : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    -- (D21 M2) the inbound path: raft's `Step` and reports, the server's `Process` and co.
    (h87 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Step.spec (GF := GF) (hG := hG))
    (h88 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h89 : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (h90 : EtcdServer.Process.spec (GF := GF) (hG := hG))
    (h91 : EtcdServer.IsIDRemoved.spec (GF := GF) (hG := hG))
    (h92 : EtcdServer.ReportUnreachable.spec (GF := GF) (hG := hG))
    (h93 : EtcdServer.ReportSnapshot.spec (GF := GF) (hG := hG))
    (h94 : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hCmpS : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    -- (the lease-revoke plan, 2026-10-31) the lessor's `Revoke`, for `isApplyLessor`'s clause
    (h95 : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    -- (2026-11-01, J8a-5) the alarm store's `Get` with no alarm, for the uber-applier's construction
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    -- (R-D1, 2026-11-04) the error paths' `b.Close()` (until then `bootOk`'s `#Hclose`)
    (hBSC : bootstrappedServer.Close.spec (GF := GF) (hG := hG)) :
    NewServer.spec (GF := GF) (hG := hG) := fun cmp =>
  -- `specG` at auth off, in the caller's compaction mode
  NewServer.wp_proofG false cmp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h10d h11 h12 h13 h14 h15 h16
    h17 h18 h19 h20 h21 h22 h23 h24 (authSrvTP_off h25 h30) trivial h26 Hp Hr hsh hfresh hopen hrest hRS hCR hSR h27 h28 h29 h31 h32 h33 h34 h35
    h36 h37 h38 h39 h41 hPeerStop hRemoteStop h42 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63
    h64 h65 h66 h67 h68 h69 h70 h71 h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83 h84 h85 h86
    h86d h86e h86f h86g h86h h87 h88 h89 h90 h91 h92 h93 h94 h95 hAG hBSC
    (fun _ => hLSR) (fun _ => hUSR) (fun _ => hUP) (fun _ => hCmpS)


end proof

end EtcdGrove
end Perennial
