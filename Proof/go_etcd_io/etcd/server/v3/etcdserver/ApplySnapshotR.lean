/-
**`applySnapshot`'s snapshot spec in restart form** (R2d'a A10, 2026-11-06; DRAFT: nothing here is
frozen, `notes/restart-plan.md`, "R2d'a A10"). Lean-first (no Rocq counterpart).

`applySnapshot.specSnapMR` is the frozen `applySnapshot.specSnapM` (`Spec/go_etcd_io/etcd/server/v3/
etcdserver/EtcdServer__applySnapshot.lean`) with the rest buckets at an image `r`, `srvRestRp E γr A r`,
in place of `srvRest E γr A` (whose image is the rest model of `A`): inside a restart window the
apply thread's rest buckets are at the replay's image (`srvRestR`'s arm, `restReplay`), which is not
the model of the ghost log. `applySnapshot` reads the old image only through `E.RO` and drops it
(`OpenSnapshotBackend` and the stores' `Recover` rebuild the rest from the snapshot's backend), so
the proof is `wp_proof_snapM`'s with the image an argument of the walk (`applySnapshot_walk`'s `r0`).
At the model it is the frozen spec (`srvRestRp_model`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The replay arm opened** (`srvRest_open`'s form at an image `r`). -/
theorem srvRestRp_open (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (r : apply.RestM) :
    srvRestRp E γr A r ⊢ ∃ f : w64 → w64, ⌜E.lg = true → leaseTTLsGeReq (appliedTable γr A) f⌝ ∗
      E.RO (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids) r) ∗
      apply.ltHalf E (srvIds E (appliedTable γr A).ids) ∗ srvGrantIf E ∗
      srvReqsIf E (appliedTable γr A) ∗ srvEver E A := by
  iintro H
  ihave ⟨H, HU⟩ := (srvRestRp_eq_at E γr A r).1 $$ H
  ihave ⟨%f, %Hf, H1, H2, H3, H4⟩ := (srvRestAt_open E _ _).1 $$ H
  iexists f
  iframe H1 H2 H3 H4 HU
  ipureintro; exact Hf

/-- In a cluster that grants none, the image's `E.RO`. -/
theorem srvRestRp_false (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (r : apply.RestM)
    (h : E.lg = false) : srvRestRp E γr A r = E.RO r := by
  unfold srvRestRp; rw [h]; rfl

end laws

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.applySnapshot(ep, ap)` with a non-empty snapshot, in restart form** (R2d'a A10, DRAFT):
`specSnapM` with the rest buckets at any image `r0` of `A`'s table (`srvRestRp E γr A r0`) in place
of the model of `A` (`srvRest E γr A`). Every other row, and the post, are `specSnapM`'s. -/
abbrev EtcdServer.applySnapshot.specSnapMR : Prop :=
  ∀
    (s ep ap sn : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai at0 dsi : w64) (nc : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk : Loc)
    (hi : uint.Z ai < uint.Z sv.Metadata'.Index')
    (d : mvcc.KBReal) (D : backend.Data) (lgh : Loc)
    (hkb : E.γ.kb = some d)
    (hdbo : storage.dbOpensOk) (hsop : storage.snapOpensOk)
    (hP : d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ ciKeys d.P ∧ storage.hooksParams d.P)
    (hcfgl : cfg.Logger' ≠ null) (hmmap : storage.openMmapOk cfg)
    (tI : w64) (hmeta : metaIs D (sv.Metadata'.Index', tI))
    (st : ApplyState) (b : GoInterface)
    (hle : uint.Z (ciEff γ st.k) ≤ uint.Z sv.Metadata'.Index')
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    -- (R2d'a A10, DRAFT) the rest buckets' image `r0`: any, at `A`'s table (`srvRestRp`)
    (r0 : apply.RestM)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl (srvObjsOn al ast lp cl d.be))
    (hwq : E.γ.watchQ = true)
    (R : mvcc.Log) (hpre : x.log <+: [[], []] ++ R) (hRok : mvcc.restoreLogOk R)
    -- (since M2's item 15) the image by the store's mode at its compaction records
    -- `r`, on past the store's compaction revision
    (r : mvcc.CmpRecs) (hcc : d.cm = true → x.crev ≤ r.crev)
    (hkI : mvcc.keyImageM d.cm ([[], []] ++ R) r D) (hbr : mvcc.bridgeParams d.P)
    -- (the lease-revoke plan, 2026-10-31) the `Lease` bucket in the table, tracked, no hook keys
    -- (the boot backend's, `bootOk`; the new backend's parameters are the old one's)
    (hlp : mvcc.leaseParams d.P)
    (γp : WTNames) (hrbw : receiptBound GF ≤ backend.wbInit - 6)
    (stp : Loc) (γd γt : GName) (img : w64 → backend.Data → IProp GF) (nt : Nat)
    (hstp : storage.storageSnap stp ss) (hnt : nt ≤ uint.nat sv.Metadata'.Index')
    (halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅)
    -- (the backend-auth-split stage) the alarm bucket in the table
    (halbi : d.P.has mvcc.alarmBI ∧
      d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI)
    (hmemb : ((backend.rbData d.P D).lookup go!"members").isSome ∧
      ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
      ((backend.rbData d.P D).lookup go!"cluster").isSome)
    (memI : GMap w64 apply.MemberM)
    (himg : membership.clusterImageOk cl (backend.rbData d.P D) memI)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (dir : w64 → List GoString)
    (ps : List w64) (idm : w64)
    (hdir : γn.dir = dir) (hdok : netDirOk dir) (hps : ∀ f, dir f ≠ [] ↔ f ∈ ps)
    (hlid : c.lid = idm)
    (msi : w64) (cs0 : Loc) (fg : GoInterface) (quota : w64) (wad : time.Duration)
    (hbuq : apply.backendUnderQuota)
    -- (S8d's named premise, S-j1's) the snapshot's entries `A'`: the rest model after them is the
    -- image's rest buckets, with the `lease` and `alarm` buckets set to empty (the rest model holds
    -- neither: their contents are the lessor's and the alarm store's), and the decoded members
    (A' : List EntryModel)
    -- (the lease-expiry plan's S2–S4, review r1 F1, 2026-11-05) in either auth mode, the image's log
    -- extends the applied one (until then the `on` arm's alone, `snapAuthImgM`)
    (hAA' : A <+: A')
    (hA' : snapRestImgM E.authOn γr d.P D A' ∧
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI)
    -- (the lease-expiry plan's S2–S4, 2026-11-05: until then the bucket empty, at a cluster that
    -- grants none) the image's lease bucket the records of its log's live leases
    (hlease : imageLeasesAt γr d.P D A')
    -- (the lease-expiry plan's S2–S4, Probe 4, DRAFT 2026-11-05) the applied log after an empty
    -- prefix (`applyAll`'s raft names) and the KV names' lease mode the environment's
    -- (`srvSnapRO`'s): what the granting walk's table lemmas take (`ImageLeases.lean`)
    (hpre0 : γr.raft.pre = []) (hlmk : E.lm = γr.kv.lm)
    -- (F9) a mode the server runs in (the convention: `EtcdServer__apply.lean:44`), and the image's
    -- auth facts by it (`off`: lean's `hauthb`; `on`: `snapRecv_imageOn`'s), in place of `hoff`
    (hany : E.authMode ≠ .any) (hauthI : snapAuthImgM E.authMode γr d.P D A A')
    -- (2026-11-01, J8a-1, item 8) the payload's two-receive `notifyc` (`rnApSnap`'s), before its
    -- first receive (until then a unit bag)
    (γnc : NotifyNames),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       isServerM E.authOn s γ ci TM E ρ γr ∗
       taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
       taNotifycAddr ap ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
       epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epDiskSnapAddr ep ↦ dsi ∗
       srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
       -- the apply thread's token, given back
       threadTok ∗
       srvCfgAddr s ↦□ cfg ∗ structFieldRef EtcdServer go!"snapshotter" s ↦□ ss ∗
       structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
       snap.isSnapshotter ss ∗ backend.fileHolds (snap.snapDBPath ss sv.Metadata'.Index') D ∗
       backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
       (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
       storage.isBackendHooks hk
         ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩ lgh ∗
       applyThread γ st ∗ applyBackend γ ci b ∗
       srvApplyKVM E.authOn s E ρ.wait x (srvAuthAtLog γr.kv srvAuthSt0 A) ∗ srvRestRp E γr A r0 ∗
       -- (S2–S4, review r1 F1) in either auth mode, the image's log committed (until then the `on`
       -- arm's alone, `snapAuthResM`)
       srvRLogLb γr.raft A' ∗
       lease.lessorInv lp E.γ.leases ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
       -- (the lease-grant plan's D2, 2026-11-02) the lessor's mode, `Recover`'s premise (the
       -- lease-expiry plan's S2–S4, Q-S5, 2026-11-05: the environment's, `srvSnapRO`'s; until then
       -- revocable, which only a cluster that grants none had)
       lease.lessorModeIs E.γ.leases (decide (E.lm = .mono)) ∗
       -- (M2's item 15) the server's closer by the mode (on, the watchable store's own parts: the
       -- store's right is the apply thread's, `srvApplyKV`'s compaction resources)
       srvKVCloserW s E ∗
       (∃ (wsl : Loc) (γw0 : mvcc.WsNames), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
        mvcc.isWatchableStore wsl E.s γw0) ∗
       mvcc.certOk E.γ ([[], []] ++ R) ∗
       -- on, the restored log's receipt and the compaction permits at the records
       mvcc.restoreRcptM d ([[], []] ++ R) ∗ mvcc.crevPermAt E.γ r.finRev ∗ mvcc.crevPermAt E.γ r.crev ∗
       □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗ srvWTPool E γp ∗
       rnStorageAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.storage.storage.ty) #stp : GoInterface) ∗
       -- (2026-11-01, J8a-1, item 8) the directory's removal fact `srvSnapRm`, as the server's
       -- bundle (`srvSnapRO`) has it (until then `snapTakenLb γt`, its first disjunct)
       inv snapDirN (snapDirInv ss γd img (srvSnapRm γt γr)) ∗ monoNatAuthOwn γt 1 nt ∗
       srvAlarmStoreAddr s ↦□ al ∗ isAlarmStore al ∗
       srvAuthStoreAddr s ↦□ auth.authIface ast ∗ srvClusterAddr s ↦□ cl ∗
       membership.isRaftCluster cl ∗
       rnTransportAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t : GoInterface) ∗
       trLive γn t c rs ∗ srvMemberIDAddr s ↦□ idm ∗
       srvMembersDir cl ps dir ∗
       epMemSnapAddr ep ↦ msi ∗ epConfState ep cs0 ∗
       srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg ∗
       srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ quota ∗
       srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ wad ∗
       -- (review R1's F1, decision 5) the apply thread's quarter
       srvStopChans γ d ∗ backend.bOpen d.γB (srvOpenQ E.authMode) ∗
       -- (F9) the auth store's `Recover` facts by the mode (`off`: `authRecoverOk`; `on`, Q2's
       -- candidate (ii): the store's invariant at the server's `E.RD` with the snapshot clause,
       -- and the image's committed log)
       snapAuthResM E.authMode s ast E.RD γr A' ∗
       -- (S8d's named premises, S-j1's: `NewServer`'s contracts of the stores on whichever backend)
       alarmApplyOk al ∗ authApplyOkM E.authMode ast E.RD ∗ lessorApplyOk lp ∗ clusterApplyOk cl ∗
       lease.lessorCfg lp ∗ lessorLookupOk lp ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ∗
       -- (J8a-4, 2026-11-01, the user's decision: `notes/decisions.md`, "J8a-4") the meta reads of
       -- a backend the apply thread opens at the protocol's names `π` over an image whose meta keys
       -- are `π.m0`, from its fresh keys and payment rights (until then of any backend at any names
       -- with `π.m0` the snapshot's, false)
       □ (∀ (π : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (D : backend.Data),
         ⌜ciKeys P ∧ metaIs D π.m0 ∧ π.bwb = γB.wb ∧ π.bopn = γB.opn⌝ -∗
         backend.hkOwn γB (backend.hkData P D) -∗ backend.bFresh γB -∗
         backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ∗
         □ ∀ (W : IProp GF) (b : Loc),
           backend.isBackend γB P W (batchLockInv (γ.withPh π) (metaTM γB P)) b -∗
           isMetaBackend (interface.mkOk (go.GoType.PointerType
             go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN)
             (readView (γ.withPh π))) }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applySnapshot")) (Val #ep))
        (Val #ap))
    {{ RET #(); srvSnapAppliedM E.authOn s ep sv γ ci E ρ γr d R r A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl ∗
      notifyRcvN γnc 1 ∗ threadTok }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`applySnapshot.specSnapMR`** (R2d'a A10, DRAFT): `wp_proof_snapM`'s proof, the rest buckets
opened by `srvRestRp_open` at the image `r0` in place of `srvRest_open` at the model of `A` (the walk
takes the image as an argument). -/
theorem EtcdServer.applySnapshot.wp_proof_snapMR
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
    (hRv : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hFS : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hRec : auth.authStore.Recover.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG)) :
    EtcdServer.applySnapshot.specSnapMR (GF := GF) (hG := hG) := by
  · intro s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmmap tI hmeta st b hle al ast lp cl x A r0 hRO hwq R hpre hRok r hcc hkI hbr hlp γp hrbw stp γd γt img nt hstp hnt halarm halbi hmemb memI himg γn t c rs dir ps idm hdir hdok hps hlid msi cs0 fg quota wad hbuq A' hAA' hA' hleaseI hpre0 hlmk hany hauthI γnc
    iintro %Φ Hpre HΦ
    icases Hpre with ⟨#Hpkg, #Hsrv, #Hsn, #Hsnap, #Hnc, #Hncb, Hrcv, Hai, Hat, Hdsi, Hlr, Hbr, Htk, #Hcfg, #Hssf, #Hhkf, #Hiss, Hfile, Hpath, #Hfg, #Hbh, Hst, Hab, HKV, HRS, #HAlb, #Hlinv, #Hlpf, #Hlrev, Hkvc, #Hkvex, #Hcok, #Hrcpt, #Hpf, #Hpc, #HkSz, #HWP, #Hstpf, #Hsdinv, Hγt, #Half, #HisAl, #Haustf, #Hclf, #Hirc, #Htrf, Htlive, #Hmidf, #Hmembers, Hmsi, Hcs0, #Hfgf, #Hfgok, #Hqbf, #Hwadf, #HoSC, HoOh, HauR, #HalA, #HauA, #HleA, #HclA, #Hlcfg, #Hllk, #Hrcn, #HmetaB⟩
    -- (the lease-expiry plan's S2–S4, 2026-11-05) a cluster that grants leases restores the image's
    -- records (`Recover` at the lessor's mode, the records `imageLeasesAt_recs`)
    cases hlgE : E.lg
    case true =>
      -- the KV invariant: auth off (with auth on a cluster grants no lease, `srvKVInvsM_lg`)
      ihave #Hsrv3 := Hsrv
      iunfold isServerM at Hsrv3
      icases Hsrv3 with ⟨-, -, -, #Hat3, -, -, -⟩
      iunfold srvAtomicsM at Hat3
      icases Hat3 with ⟨-, -, #HkM⟩
      ihave %Hon := srvKVInvsM_lg _ _ _ _ $$ HkM
      have hklg : γr.kv.lg = true := by
        rw [KVNames.lg_eq, ← hlmk, ← apply.AEnv.lg_eq]; exact hlgE
      have hon : E.authOn = false := by
        cases hao : E.authOn
        · rfl
        · rw [Hon hao] at hklg; cases hklg
      have ekv : srvKVInvsM (GF := GF) E.authOn s E γr = srvKVInvs E γr := by rw [hon]; rfl
      ihave #HkO : srvKVInvs E γr $$ []
      · rw [← ekv]; iexact HkM
      iunfold srvKVInvs at HkO
      icases HkO with ⟨#HkI, -, #HrI, -⟩
      imod kv_log_plain γr.raft γr.kv A' $$ HkI HrI HAlb with %Hpl0
      imod kv_grantLog_nodup γr.raft γr.kv A' $$ HkI HrI HAlb with %Hnd
      -- the apply thread's rest buckets, opened
      ihave ⟨%f0, %Hf0, HRO, HL0, #HGI, #HRq, HEv⟩ := srvRestRp_open E γr A r0 $$ HRS
      ihave ⟨%U, HEvU, %HUok⟩ := srvEver_open E A $$ HEv
      have hsI : ∀ X : List w64, srvIds E X = X := fun X => by simp [srvIds, hlgE]
      have eG : srvGrantIf (GF := GF) E = srvGrantable E := by
        unfold srvGrantIf; rw [hlgE]; rfl
      have eQ : srvReqsIf (GF := GF) E (appliedTable γr A) = srvReqs E (appliedTable γr A) := by
        unfold srvReqsIf; rw [hlgE]; rfl
      ihave #HGr : srvGrantable E $$ []
      · rw [← eG]; iexact HGI
      ihave #HRq2 : srvReqs E (appliedTable γr A) $$ []
      · rw [← eQ]; iexact HRq
      iunfold srvGrantable at HGr
      icases HGr with ⟨#HGall, -⟩
      iunfold srvReqs at HRq2
      -- the image's records (`imageLeasesAt_recs`) and their TTLs
      obtain ⟨recs, hbe, hperm', -, hge⟩ := imageLeasesAt_recs hleaseI
      obtain ⟨f, hfT, hfb⟩ := hleaseI
      have hnT' : (appliedTable γr A').ids.Nodup := appliedTable_nodup γr A'
      have hmodes : E.lm = .mono ∨ E.lm = .revocable := by
        have hc := hlgE
        rw [apply.AEnv.lg_eq] at hc
        revert hc
        cases E.lm
        · intro hc; simp at hc
        · intro _; exact Or.inl rfl
        · intro _; exact Or.inr rfl
      have hpl : E.lm = .mono → plainLogM γr.kv.cmp .mono A' := fun h => by
        have := Hpl0.1; rw [← hlmk, h] at this; exact this
      have hnd' : E.lm = .revocable → (srvGrantLog A').Nodup := fun h => Hnd (by rw [← hlmk]; exact h)
      -- (S2, F7) a record whose id the lessor had is the applied table's lease, its request the table's
      have hUq : (decide (E.lm = .mono) = true → ∀ u ∈ U, u ∈ srvIds E (appliedTable γr A).ids) →
          ∀ x ∈ recs, x.1 ∈ U → ∃ q ∈ appliedTable γr A, q.1 = x.1 ∧
            q.2 = tableReq (appliedTable γr A') x.1 := by
        intro hmU x hx hxU
        have hxT' : x.1 ∈ (appliedTable γr A').ids := hperm'.mem_iff.1 (List.mem_map.2 ⟨x, hx, rfl⟩)
        obtain ⟨q, hq, hq1⟩ := List.mem_map.1 hxT'
        refine ⟨q, ?_, hq1, ?_⟩
        · rcases hmodes with hm | hm
          · have hxT : x.1 ∈ (appliedTable γr A).ids := by
              have := hmU (by simp [hm]) x.1 hxU; rwa [hsI] at this
            obtain ⟨q0, hq0, hq01⟩ := List.mem_map.1 hxT
            have hq0' := appliedTable_mono_mem γr hAA' (hpl hm) q0 hq0
            have heq := table_eq_of_id hnT' hq0' hq (hq01.trans hq1.symm)
            rw [← heq]; exact hq0
          · exact appliedTable_rev_mem γr hAA' (hnd' hm) q
              (by rw [hq1]; exact HUok.2 hm x.1 hxU) hq
        · rw [← hq1, tableReq_of_mem hnT' hq]
      have hrmono : decide (E.lm = .mono) = true →
          ∀ id ∈ srvIds E (appliedTable γr A).ids, id ∈ recs.map (·.1) := by
        intro hm id hid
        rw [hsI] at hid
        exact hperm'.mem_iff.2 (appliedTable_mono_sub γr hAA' (hpl (of_decide_eq_true hm)) id hid)
      have hrUL : decide (E.lm = .mono) = false →
          ∀ id ∈ recs.map (·.1), id ∈ U → id ∈ srvIds E (appliedTable γr A).ids := by
        intro hm id hid hU
        rw [hsI]
        have hr : E.lm = .revocable := by
          rcases hmodes with h | h
          · simp [h] at hm
          · exact h
        exact appliedTable_granted_live γr hAA' (hnd' hr) id (HUok.2 hr id hU) (hperm'.mem_iff.1 hid)
      have hreq : ∀ x ∈ recs, sint.Z (tableReq (appliedTable γr A') x.1) ≤ sint.Z x.2.1 := by
        intro x hx
        obtain ⟨q, hq, hq1⟩ := List.mem_map.1 (hperm'.mem_iff.1 (List.mem_map.2 ⟨x, hx, rfl⟩))
        rw [← hq1, tableReq_of_mem hnT' hq]
        exact hge x hx q hq hq1
      have hperm : (srvIds E (appliedTable γr A').ids).Perm (recs.map (·.1)) := by
        rw [hsI]; exact hperm'.symm
      -- the walk's lessor premises
      ihave #HRqs : □ (⌜decide (E.lm = .mono) = true → ∀ u ∈ U, u ∈ srvIds E (appliedTable γr A).ids⌝ -∗
          [∗list] x ∈ recs, ⌜x.1 ∉ U⌝ ∨
            lease.leaseReqIs E.γ.leases x.1 (tableReq (appliedTable γr A') x.1)) $$ []
      · iintro !> %hmU
        have key : □ (∀ p : w64 × w64, ⌜p ∈ appliedTable γr A⌝ -∗
            lease.leaseReqIs E.γ.leases p.1 p.2) ⊢
            [∗list] x ∈ recs, (⌜x.1 ∉ U⌝ ∨
              lease.leaseReqIs (GF := GF) E.γ.leases x.1 (tableReq (appliedTable γr A') x.1)) := by
          apply BigSepL.bigSepL_intro
          intro k x hk
          refine intuitionistically_elim.trans ?_
          iintro #H
          by_cases hxU : x.1 ∈ U
          · obtain ⟨q, hq, hq1, hq2⟩ := hUq hmU x (List.mem_of_getElem? hk) hxU
            iright
            rw [← hq2, ← hq1]
            iapply H; ipureintro; exact hq
          · ileft; ipureintro; exact hxU
        iapply key
        iexact HRq2
      ihave #HGrs : □ ([∗list] id ∈ recs.map (·.1), lease.leaseGranted E.γ.leases id) $$ []
      · iintro !>
        have key : □ (∀ id : w64, lease.leaseGranted (GF := GF) E.γ.leases id) ⊢
            [∗list] id ∈ recs.map (·.1), lease.leaseGranted E.γ.leases id := by
          apply BigSepL.bigSepL_intro
          intro k x hk
          refine intuitionistically_elim.trans ?_
          iintro #H; iapply H
        iapply key; iexact HGall
      iapply wp_fupd
      iapply (applySnapshot_walk hIES hLg hInfo hU64 hGI hGT hOSB hOn hSave hPut hBUR hID hName hSafe s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmmap tI hmeta hSB st b hle hLR al ast lp cl x A hRO hany (fun _ => authRecoverOn_glue hRec) (decide (E.lm = .mono)) recs U
        (tableReq (appliedTable γr A')) (srvIds E (appliedTable γr A').ids)
        (srvIds E (appliedTable γr A).ids) hbe hrmono hrUL (fun _ => hlgE) hreq hperm
        (fun h => by rw [hlgE] at h; cases h)
        (apply.restLeasesWith f0 (srvIds E (appliedTable γr A).ids) r0) hwq hRst hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL hCB hDel R hpre hRok r hcc hkI hbr hGTP hSTP hCIg γp hrbw hRel stp γd γt img nt hstp hnt hNAB hAR halarm halbi hlp hNAuB A' hauthI hAA' hNMB hCSB hmemb hClose hCRec memI himg hRAP hAP hMID γn t c rs dir ps idm hdir hdok hps hlid hNUA msi cs0 fg quota wad hbuq γnc hAG hLSR hUSR hWrite hTODO) $$ [Hrcv Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRO HL0 HEvU Hkvc Hγt Htlive Hmsi Hcs0 HoOh Htk HauR]
      · iframe #
        iframe Hrcv Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRO HL0 HEvU Hkvc Hγt Htlive Hmsi Hcs0 HoOh Htk HauR
      iintro !> ⟨Hw, Hrcv, Htk⟩
      have hUok' : srvEverOk E A' (U ++ recs.map (·.1)) := by
        refine ⟨fun h => (by rw [hlgE] at h; cases h), fun hr u hu => ?_⟩
        rcases List.mem_append.1 hu with h | h
        · exact srvGrantLog_prefix hAA' u (HUok.2 hr u h)
        · exact appliedTable_ids_granted γr hpre0 A' u (hperm'.mem_iff.1 h)
      have hbkG := snap_bkG E.authMode γr d.P D A' hany hA'.1 f (srvIds E (appliedTable γr A').ids)
        (by rw [hsI]; exact hfb)
      have hreqT : E.lg = true → ∀ p ∈ appliedTable γr A', ∃ x ∈ recs, x.1 = p.1 ∧
          tableReq (appliedTable γr A') x.1 = p.2 := by
        intro _ p hp
        obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hperm'.mem_iff.2 (List.mem_map.2 ⟨p, hp, rfl⟩))
        exact ⟨x, hx, hx1, by rw [hx1, tableReq_of_mem hnT' hp]⟩
      ihave Hpost := (srvSnapApplied_of_walk hGL hAt hDt hSRD hLk hGrant hCk hTTL hRv hMID hLead hTerm hFS hCIg s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl tI hmeta st b hle al ast lp cl x A hRO hwq R hpre hRok r hkI hbr hlp γp hrbw stp γd γt img nt hstp hnt halarm hmemb memI himg γn t c rs dir ps idm hdir hdok hps hlid msi cs0 fg quota wad hbuq A' hA' hany (srvIds E (appliedTable γr A').ids) recs U
        (tableReq (appliedTable γr A')) f rfl hUok' hbkG (fun _ => hfT) hreqT) $$ [Hw]
      · iframe #
        iframe Hw
      imod Hpost
      imodintro
      iapply HΦ
      iframe Hrcv Htk
      iapply (srvSnapAppliedM_of_G s ep sv γ ci E ρ γr d R r A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl hany)
      iexact Hpost
    -- a cluster that grants none (`specSnapM`'s premise until S2–S4): the image's lease bucket
    -- empty, the lessor revocable
    have Hlg0 := hlgE
    -- (review r2 S1) the image's log grants none: its committed log is plain in the mode (auth
    -- off: `kv_log_plain` at the lease mode `.none`; on: `kv_log_plainOn`)
    have hlm0 : γr.kv.lm = .none := by rw [← hlmk]; exact apply.AEnv.lm_of_lg_false hlgE
    ihave #Hsrv4 := Hsrv
    iunfold isServerM at Hsrv4
    icases Hsrv4 with ⟨-, -, -, #Hat4, -, -, -⟩
    iunfold srvAtomicsM at Hat4
    icases Hat4 with ⟨-, -, #HkM⟩
    ihave Hnil : |={⊤}=> ⌜(appliedTable γr A').ids = []⌝ $$ []
    · by_cases hon : E.authOn = true
      · have ekv : srvKVInvsM (GF := GF) E.authOn s E γr =
            iprop(srvKVInvsOn E γr srvAuthSt0 ∗ srvUberOn s) := by rw [hon]; rfl
        ihave #HkO : iprop(srvKVInvsOn E γr srvAuthSt0 ∗ srvUberOn s) $$ []
        · rw [← ekv]; iexact HkM
        icases HkO with ⟨#HkO, -⟩
        iunfold srvKVInvsOn at HkO
        icases HkO with ⟨#HkI, -, #HrI, -⟩
        imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A' $$ HkI HrI HAlb with %Hpl
        imodintro; ipureintro
        unfold appliedTable kvLeases; rw [hpre0, List.nil_append, kvTableOf_plainOn _ _ A' Hpl]; rfl
      · have ekv : srvKVInvsM (GF := GF) E.authOn s E γr = srvKVInvs E γr := by
          rw [show E.authOn = false by simpa using hon]; rfl
        ihave #HkO : srvKVInvs E γr $$ []
        · rw [← ekv]; iexact HkM
        iunfold srvKVInvs at HkO
        icases HkO with ⟨#HkI, -, #HrI, -⟩
        imod kv_log_plain γr.raft γr.kv A' $$ HkI HrI HAlb with %Hpl0
        imodintro; ipureintro
        have Hpl' : plainLogM γr.kv.cmp .none A' := hlm0 ▸ Hpl0.1
        unfold appliedTable kvLeases
        rw [hpre0, List.nil_append, kvTableOf_plainM _ _ _ A' Hpl']; rfl
    imod Hnil with %hTnil
    have hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅ :=
      imageLeasesAt_nil hTnil hleaseI
    ihave #Hlrev2 : lease.lessorRevocable E.γ.leases $$ []
    · have heq : lease.lessorModeIs (GF := GF) E.γ.leases (decide (E.lm = .mono)) =
          lease.lessorRevocable E.γ.leases := by
        rw [apply.AEnv.lm_of_lg_false hlgE]; rfl
      rw [← heq]; iexact Hlrev
    ihave HRS : E.RO r0 $$ [HRS]
    · rw [← srvRestRp_false E γr A r0 Hlg0]; iexact HRS
    have hbe0 : backend.bktEnts (((backend.rbData d.P D).lookup go!"lease").getD ∅) =
        ([] : List (w64 × w64 × w64)).map lease.leaseRecEnc := by
      rw [hlease]
      exact List.eq_nil_of_length_eq_zero ((mvcc.bktEnts_length ∅).trans GMap.map_size_empty)
    have hids : srvIds E (appliedTable γr A').ids = [] := by simp [srvIds, hlgE]
    have hLr : ([] : List w64) = srvIds E (appliedTable γr A').ids := hids.symm
    have hUok : srvEverOk E A' (([] : List w64) ++ ([] : List (w64 × w64 × w64)).map (·.1)) :=
      ⟨fun _ => rfl, fun _ u hu => by simp at hu⟩
    have hbkG : ∀ n, membership.clusterBkts n ∨ restSet E.authMode n →
        (apply.restLeasesWith (fun _ => 0) (srvIds E (appliedTable γr A').ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup n =
        (<[go!"alarm" := ∅]> (<[go!"lease" := ((backend.rbData d.P D).lookup go!"lease").getD ∅]>
          (backend.rbData d.P D))).lookup n := by
      intro n hn
      rw [hids, apply.restLeasesWith_nil, hlease]
      exact snapRestImgM_bk E.authMode γr d.P D A' hany hA'.1 n hn
    iapply wp_fupd
    iapply (applySnapshot_walk hIES hLg hInfo hU64 hGI hGT hOSB hOn hSave hPut hBUR hID hName hSafe s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmmap tI hmeta hSB st b hle hLR al ast lp cl x A hRO hany (fun _ => authRecoverOn_glue hRec) false [] [] (fun _ => 0) [] []
      hbe0 (fun h => by cases h) (by simp) (fun h => by cases h) (by simp) List.Perm.nil
      (fun _ => ⟨rfl, rfl⟩) r0 hwq hRst hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL hCB hDel R hpre hRok r hcc hkI hbr hGTP hSTP hCIg γp hrbw hRel stp γd γt img nt hstp hnt hNAB hAR halarm halbi hlp hNAuB A' hauthI hAA' hNMB hCSB hmemb hClose hCRec memI himg hRAP hAP hMID γn t c rs dir ps idm hdir hdok hps hlid hNUA msi cs0 fg quota wad hbuq γnc hAG hLSR hUSR hWrite hTODO) $$ [Hrcv Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRS Hkvc Hγt Htlive Hmsi Hcs0 HoOh Htk HauR]
    · iframe #
      iframe Hrcv Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRS Hkvc Hγt Htlive Hmsi Hcs0 HoOh Htk HauR
      rw [apply.ltHalf_false E [] hlgE, apply.everOwn_false E [] hlgE]
      simp only [List.map_nil]
      isplitr; · itrivial
      isplitr; · itrivial
      isplitr; · iintro !> -; iapply BigSepL.bigSepL_nil; iempintro
      iintro !>; iapply BigSepL.bigSepL_nil; iempintro
    iintro !> ⟨Hw, Hrcv, Htk⟩
    ihave Hpost := (srvSnapApplied_of_walk hGL hAt hDt hSRD hLk hGrant hCk hTTL hRv hMID hLead hTerm hFS hCIg s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl tI hmeta st b hle al ast lp cl x A hRO hwq R hpre hRok r hkI hbr hlp γp hrbw stp γd γt img nt hstp hnt halarm hmemb memI himg γn t c rs dir ps idm hdir hdok hps hlid msi cs0 fg quota wad hbuq A' hA' hany [] [] [] (fun _ => 0) (fun _ => 0) hLr hUok hbkG
      (fun h => by rw [hlgE] at h; cases h) (fun h => by rw [hlgE] at h; cases h)) $$ [Hw]
    · iframe #
      iframe Hw
      unfold srvGrantIf; rw [hlgE]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    imod Hpost
    imodintro
    iapply HΦ
    iframe Hrcv Htk
    iapply (srvSnapAppliedM_of_G s ep sv γ ci E ρ γr d R r A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl hany)
    iexact Hpost


end proof

end EtcdGrove
end Perennial
