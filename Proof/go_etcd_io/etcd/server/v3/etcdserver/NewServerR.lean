/-
`NewServer(cfg)` at a restart: `NewServer.wp_proofR`, the proof of `NewServer.specR`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean`). Lean-first.

(Restart S6 B2, 2026-11-14, decided by etcd-grove-81: D1's fallback, `notes/decisions.md`, "Restart S6
B2") A separate proof, not a `SrvBoot` instance of `NewServer.wp_proofG`: the first-start proof's boot
steps (the bootstrap contract, the WAL, the node, the store, the snapshot directory, the apply rows) are
replaced by the restart's (`bootstrapRestartContract`, `wal.restartOk_start`, `raftNode_of_RestartNode`,
`boot_storageR`, the image's directory invariant and counter), and the tail follows `wp_proofG`'s. In
its own module: `NewServer.lean`'s compile has reached 80 GB. Not linked until it has no `sorry`.
Follow-up: factor the shared tail of the two proofs.

STATUS: skeleton (the statement); the proof is not written.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuiltRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerRFacts

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

/-- `bootstrap`'s restart contract is persistent (as `bootstrapContract`). -/
instance bootstrapRestartContract_persistent [MemStorReg GF] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (U : BootURLs) (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) :
    Persistent (bootstrapRestartContract (GF := GF) cfg U γ id N dir) := by
  unfold bootstrapRestartContract; infer_instance

/-- **`NewServer(cfg)` at a restart** (`NewServer.specR`), over `wp_proofG`'s callee specs at auth
off and no compaction (the restart's scope). Skeleton: not yet proved. -/
theorem NewServer.wp_proofR
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
    (hTP : authSrvTP (GF := GF) (hG := hG) false)
    -- (step 6 of the auth-mode merge) what the uber-applier's contracts with auth on are built from
    (hKit : uberKitM (GF := GF) (hG := hG) false)
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
    NewServer.specR (GF := GF) (hG := hG) := by
  haveI := Hp.1
  intro cfg U γ id ρ ρo E₀ N Φs γn dir m S σ i A D mb M HρRaft HrN Hrule Hc0 Hch0 Hlog0 Hkcmp Hcbl
    Hmrb Hmto Hcb Hcmp0 HNx0 Hbnd Hrb HrbN Hboot Hpfx HΦs Hfgp Hdirok HpU Hrnc Hdirs Hlbc Hbco Hfnc
    Hdwd Hbwb
  have Hslg : ∃ m' : lease.Mode, lease.runCfg (GF := GF) ρ.rd.kv.lm m' := ⟨m, lease.bootCfg_run Hlbc⟩
  replace Hbnd : threadBound GF ≤ 2 ^ 28 := Hbnd
  -- the stopped names' raft names the restarted ones (`restartNames`)
  have Hρo : ρo.rd.raft = ⟨γ, [], W64 0⟩ := by rw [← HrN.1]; exact HρRaft
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
  -- the stopped member's image
  iunfold srvDiskImageAt at Himg
  icases Himg with ⟨Hvac, HrS, %Himr, #HA, %Himp, ⟨%u, #Hmvi⟩, %Hbl, #Hconf, %Hcsm, Hwsi, Hrauth,
    Hfiles, Hpath, Hsdimg⟩
  rw [Hρo] at Himp
  ihave #HA0 : srvRLogLb ⟨γ, [], W64 0⟩ A $$ []
  · rw [← Hρo]; iexact HA
  obtain ⟨Hiz, Himg, Hist⟩ := Himp
  simp only [List.nil_append] at Himg
  have HiA : uint.nat i = A.length := by simp at Hiz; word
  icases wal.stopImage_elim _ _ _ _ $$ Hwsi with ⟨%Hsw, #Hcert, ⟨%l', #Hl', %Hl'b, %Hag⟩⟩
  -- the contract's antecedents: the cluster version (`restart_clusterVerLogOk`) and the members'
  -- peer URLs at `A` the boot log's (clause (G), `restart_peerURLs`)
  ihave #HkvI : kvInv ρ.rd.raft ρ.rd.kv $$ []
  · rw [← kvInvM_false]; iexact Hkvinv
  imod restart_clusterVerLogOk ρ.rd.raft ρ.rd.kv A (by rw [HρRaft]) $$ HkvI Hsrl [] with %Hcvl
  · rw [HρRaft]; iexact HA0
  rw [HρRaft] at Hcvl
  simp only [List.nil_append] at Hcvl
  imod restart_peerURLs ρ.rd.raft ρ.rd.kv A (by rw [HρRaft]) $$ HkvI Hsrl [] with %Hpurl
  · rw [HρRaft]; iexact HA0
  rw [HρRaft] at Hpurl
  -- `bootstrap`'s restart contract at the image
  ihave #Hboot' := HbootR
  iunfold bootstrapRestartContract at Hboot'
  ihave Hbc := Hboot' $$ %σ %i %A %D %M [] []
  · ipureintro
    exact ⟨Hsw.2.1, Hsw.2.2, Hbl, Hbco, Hfnc, Hdwd, Hdisk.1, Hdisk.2.2.1, Hbwb, Hpurl, Hcvl⟩
  · iexists ρo.rd.kv, A, u
    iframe Hmvi
    ipureintro; exact ⟨Himr.2, Himg, Hist⟩
  wp_apply Hbc $$ [Hrauth Hfiles Hpath] as %b %err Hb
  · iframe; iframe Hcfgro Hzlg Hvoff
    iright; iexact Hfg
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
    · iexact Hzlg
    iapply HΦ
    ileft
    iframe Htok
    ipureintro; exact ⟨rfl, Herr⟩
  subst Herr
  iNamed Hb
  -- (premise fixes 5) the Key bucket's size bound, proved
  ihave #Hsz := mvcc.keySized_at (GF := GF) d.P
  -- the restart's indices (probe P6): `σ.b ≤ |A| ≤ σ.commit`, `bootLen ≤ σ.commit`
  obtain ⟨Hba, Hac, Hblc⟩ := restart_idx σ i (W64 0) A γ.cl.bootLen (by simp at Hiz ⊢; word) rfl
    Hsw.2.1 Hsw.2.2 Hbl
  -- the WAL: its read facts, and its durability at the restart's view (`wal.restartOk_start`) over
  -- the committed log up to the records' base
  icases wal.restartOk_facts _ _ _ _ _ $$ Hwal with ⟨Hwal, %Hwrf⟩
  have Hl0len : (srvLE ⟨γ, [], W64 0⟩ (A.take σ.b)).length = σ.b := by
    simp [srvLE]; omega
  ihave #Hl0 : isCommittedLogLb γ.cl (srvLE ⟨γ, [], W64 0⟩ (A.take σ.b)) $$ []
  · ihave #HA0' := HA0
    iunfold srvRLogLb at HA0'
    icases HA0' with ⟨#H, -⟩
    iapply isCommittedLogLb_mono _ _ _ ?_ $$ H
    simp only [srvLE, List.nil_append, List.map_take]
    exact List.take_prefix _ _
  ihave Hwsi := wal.stopImage_intro γ.cl S σ i Hsw.1 Hsw.2.1 Hsw.2.2 $$ [Hcert Hl']
  · iframe Hcert
    iexists l'
    iframe Hl'
    ipureintro; exact ⟨Hl'b, Hag⟩
  imod wal.restartOk_start cfg id cid bw.w' σ γ.cl S i _ Hl0len $$ [Hwal Hwsi Hl0] with
    ⟨%νw, #Hdur, Hwview, Hwok, Hwstop, Hwapp, #Hwlb, Hwsi, Hwalo, %HwalR, Hwmeta, Hwpurge, %HwDir⟩
  · iframe Hwal Hwsi Hl0
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
  · iexact Hzlg
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
  -- `b.raft.newRaftNode(b.ss, b.storage.wal.w, b.cluster.cl)`: raft's node restarted
  -- (`NodeStartSpecR`, `raftNode_of_RestartNode`)
  have hNS := raftNode_of_RestartNode (GF := GF) h8 h86d h85 h86e h86f h86g h86h h9 h10 h11 h10d h12
    h87 h88 h89 h78 h86
  obtain ⟨Hrcfg, Hrhb, Hrlg, Hrid, Hrps, Hrnodup, Hr0, Hrmem, Hrvs, Hrbok⟩ := Hraft
  ihave #Hrzl : zapLoggerOk bv.lg' $$ []
  · rw [Hrlg]; iexact Hzlg
  have Hdirps : (∀ f, dir f ≠ [] ↔ f ∈ ps) ∧ ps.length ≤ 2 ^ 20 :=
    ⟨fun f => by rw [← Hrvs]; exact rafthttp.bootCfg_mem Hdirs f,
      by rw [← Hrvs]; exact rafthttp.bootCfg_len Hdirs⟩
  have Hrpslen : (ps.length : Int) < 2 ^ 62 := by have := Hdirps.2; omega
  imod (srvSendKey_alloc (GF := GF)) with ⟨%γk, Hk⟩
  -- the backend's conf state the voters' (the image's, D4): the membership at `|A|` is the voters'
  icases Hrest with ⟨%cs, %Hcs, Hrest⟩
  ihave #Hsrl0 : srvRaftLogInv ⟨γ, [], W64 0⟩ $$ []
  · rw [← HρRaft]; iexact Hsrl
  ihave #HAc : isCommittedLogLb γ.cl (srvLE ⟨γ, [], W64 0⟩ A) $$ []
  · ihave #HA0' := HA0
    iunfold srvRLogLb at HA0'
    icases HA0' with ⟨#H, -⟩
    iexact H
  ihave #HconfA : confAt γ.cl A.length mb $$ []
  · rw [← HiA]; iexact Hconf
  imod srv_confAt_eq_simple ⟨γ, [], W64 0⟩ (srvLE ⟨γ, [], W64 0⟩ A) A.length mb (by simp [srvLE]) ⊤
    (by simp) (by simp) $$ [$Hsrl0 $HAc $HconfA] with %Hmb
  have Hcfg0 : W64 0 ∉ γ.cfg := fun h0 => Hr0 (by
    unfold SrvRaft.cfg at h0; rw [Hrvs] at h0; exact (GMap.elem_of_list_to_set _ _).1 h0)
  have Hcfgsz : GMap.size γ.cfg < 2 ^ 62 := by
    unfold SrvRaft.cfg; rw [Hrvs, GMap.size_list_to_set ps Hrnodup]; omega
  have Hcsv : confStateIs cs (Membership.simple γ.cfg) := by rw [← Hmb]; exact Hcsm cs Hcs
  ihave #Hclu : isCluster γ.cl srvClusterN $$ []
  · iunfold srvRaftLogInv at Hsrl0
    icases Hsrl0 with ⟨-, Hco, -⟩
    iunfold srvClusterOk at Hco
    icases Hco with ⟨#H, -⟩
    iexact H
  ihave #Hrf : readyFits γ.cl srvClusterN $$ []
  · iunfold srvRaftLogInv at Hsrl0
    icases Hsrl0 with ⟨-, Hco, -⟩
    iunfold srvClusterOk at Hco
    icases Hco with ⟨-, -, -, #H, -⟩
    iexact H
  ihave Hvac : nodeVacant γ.cl cv.ID' $$ [Hvac]
  · rw [Hrid]; iexact Hvac
  ihave HrS : raftState γ.cl cv.ID' S $$ [HrS]
  · rw [Hrid]; iexact HrS
  ihave #Hctx : peersCtx pv ([] : List (List w8)) $$ []
  · rw [Hrcfg.peersNil]; iunfold peersCtx; iapply BigSepL2.bigSepL2_nil.2; itrivial
  wp_apply (hNS γ (srvErM false ρ E₀ (W64 0) (W64 0) (restartKV ρ.rd.kv A) id (srvTrKey γn γk)
      (srvTrStopK γk)) bs.raft' bs.ss' bw.w' bc.cl' (DFrac.own 1) bv cv lok γs νw pv [] ρ.ids.issued
      σ cs S mb A)
    $$ [Hbv Hc Hrest Hpeers Hvac HrS Hwview Hwok]
    as %r ⟨%γrn, %rvr, %Hrnames, Hr, Hrtm, #HstepI, Hloop, Happly, Hrunh, Hinst, Hbv, -, #Hminv,
      Hmsmeta, Hrsc⟩
  · iframe Hbv Hc Hrest Hpeers Hvac HrS Hwview Hwok
    iframe #
    ipureintro
    exact ⟨⟨Hrcfg, by rw [Hrhb]; exact raftNode.bootCfg_heartbeat cfg Hrnc, HwalR, by omega, Hcfg0,
      Hcfgsz, Hba, Hac, Hblc, Hsw.1, walReadFacts_F3 σ Hwrf, Hcsv,
      restart_cs_bound cs γ.cfg Hcsv Hcfgsz⟩, Hγsz⟩
  sorry

end proof

end EtcdGrove
end Perennial
