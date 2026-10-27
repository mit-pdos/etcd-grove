/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13): no snapshot. D22 receiver epochs, S8d
(2026-10-26): a non-empty snapshot, `applySnapshot_walk` (`SnapApplyWalk.lean`) and
`srvSnapApplied_of_walk` (`SnapApplyPost.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyWalk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyPost

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem EtcdServer.applySnapshot.wp_proof
    (hIES : IsEmptySnap.spec (GF := GF) (hG := hG)) :
    EtcdServer.applySnapshot.spec (GF := GF) (hG := hG) := by
  intro s ep ap
  wp_start as #Hsn
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_IsEmptySnap_nil hIES) $$ [$Hrpkg]
  (try wp_auto)
  iapply HΦ
  itrivial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`applySnapshot` with a non-empty snapshot** (S8d): `specSnap`, from its callees' specs. Not
linked yet: S-j1 wires it into `applyAll` (`notes/snapshot-s8-plan.md`, "For S-j1"). -/
theorem EtcdServer.applySnapshot.wp_proof_snap
    (hIES : IsEmptySnap.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (hOSB : storage.OpenSnapshotBackend.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hBUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hSB : consistentIndex.SetBackend.spec (GF := GF) (hG := hG))
    (hLR : lease.lessor.Recover.spec (GF := GF) (hG := hG))
    (hRst : mvcc.watchableStore.Restore.spec (GF := GF) (hG := hG))
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hGTP : EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hSTP : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hRel : storage.storage.Release.spec (GF := GF) (hG := hG))
    (hNAB : schema.NewAlarmBackend.spec (GF := GF) (hG := hG))
    (hAR : v3alarm.AlarmStore.Recover.spec (GF := GF) (hG := hG))
    (hNAuB : schema.NewAuthBackend.spec (GF := GF) (hG := hG))
    (hNMB : schema.NewMembershipBackend.spec (GF := GF) (hG := hG))
    (hCSB : membership.RaftCluster.SetBackend.spec (GF := GF) (hG := hG))
    (hClose : backend.backend.Close.spec (GF := GF) (hG := hG))
    (hCRec : membership.RaftCluster.Recover.spec (GF := GF) (hG := hG))
    (hRAP : rafthttp.Transport.RemoveAllPeers.spec (GF := GF) (hG := hG))
    (hAP : rafthttp.Transport.AddPeer.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hNUA : EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG))
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hFS : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG)) :
    EtcdServer.applySnapshot.specSnap (GF := GF) (hG := hG) := by
  · intro s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmeta st b hle al ast lp cl x A hRO hlease hwq R hpre hRok hkI hbr γp hrbw stp γd γt img nt hstp hnt halarm hauthb hmemb memI himg γn t c rs dir ps idm hdir hdok hps hlid msi cs0 fg quota wad Tal zal hbuq A' hA' hoff
    iintro %Φ Hpre HΦ
    icases Hpre with ⟨#Hpkg, #Hsrv, #Hsn, #Hsnap, #Hnc, #Hncb, Hai, Hat, Hdsi, Hlr, Hbr, #Hcfg, #Hssf, #Hhkf, #Hiss, Hfile, Hpath, #Hfg, #Hbh, Hst, Hab, HKV, HRS, #Hlinv, #Hlpf, Hkvc, #Hkvex, #Hcok, #HkSz, #HWP, #Hstpf, #Hsdinv, Hγt, #Half, #HisAl, #Haustf, #Hclf, #Hirc, #Htrf, Htlive, #Hmidf, HR8s, #Hmembers, Hmsi, Hcs0, #Hfgf, #Hfgok, #Hqbf, #Hwadf, #HalG, HTal, #HoSC, HoOh, #HauR, #HalA, #HauA, #HleA, #HclA, #Hlcfg, #Hllk, #Hrcn, HRD2, #HmetaB⟩
    iapply wp_fupd
    iapply (applySnapshot_walk hIES hLg hInfo hU64 hGI hGT hOSB hOn hSave hPut hBUR hID hName hSafe s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmeta hSB st b hle hLR al ast lp cl x A hRO hlease hwq hRst hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL hCB hDel R hpre hRok hkI hbr hGTP hSTP hCIg γp hrbw hRel stp γd γt img nt hstp hnt hNAB hAR halarm hNAuB hauthb hNMB hCSB hmemb hClose hCRec memI himg hRAP hAP hMID γn t c rs dir ps idm hdir hdok hps hlid hNUA msi cs0 fg quota wad Tal zal hbuq) $$ [Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRS Hkvc Hγt Htlive HR8s Hmsi Hcs0 HTal HoOh]
    · iframe #
      iframe Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRS Hkvc Hγt Htlive HR8s Hmsi Hcs0 HTal HoOh
    iintro !> Hw
    ihave Hpost := (srvSnapApplied_of_walk hGL hAt hDt hSRD hLk hGrant hCk hTTL hMID hLead hTerm hFS hCIg s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmeta st b hle al ast lp cl x A hRO hlease hwq R hpre hRok hkI hbr γp hrbw stp γd γt img nt hstp hnt halarm hauthb hmemb memI himg γn t c rs dir ps idm hdir hdok hps hlid msi cs0 fg quota wad Tal zal hbuq A' hA' hoff) $$ [Hw HRD2]
    · iframe #
      iframe Hw HRD2
    imod Hpost
    imodintro
    iapply HΦ
    iexact Hpost

end proof

end EtcdGrove
end Perennial
