/-
**`applySnapshot`'s code past the empty case** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`): `applySnapshot_walk`, the walk through the code from the spec's
premises to `snapWalkPost` (`SnapApplyDefs.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AlarmGet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClientLaws
-- (the lease-expiry plan's step 2) the range deleter's argument, `traceutil.TODO()`
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open mvcc.api (mvccLeases)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`applySnapshot`'s code, past the empty case** (S8d): from its premises to `snapWalkPost`.
(Strict M1, 2026-11-06: the store restored by `KV.Restore.contract` at its dynamic type
(`shapes.law`), its precondition `restoreArgs_holds`'s; the new backend opened for it by
`etcdStorage_open.law` at the registration `mvccW_alloc.law` gives; until then mvcc's internal
`watchableStore.Restore` over the backend's own specs.)
(The mvcc merge, 2026-11-06: `lean`'s walk (the auth-on pair's mode-generic walk, P6.2; the
lease-expiry plan's `Recover` of the image's records; R2b-3c/3d's stop channels and file) with
strict M1's store part over the API; R4, 2026-11-07: checked, the store restored at `Recover`'s
live set `Lr` (the image's history attaching no lease, `hnl`), the deleter rebuilt from
`KV.Write.contract`.) -/
theorem applySnapshot_walk [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
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
    -- (strict M1) mvcc's laws
    (Hp : mvcc.api.persistent.law (GF := GF)) (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hWA : mvcc.api.mvccW_alloc.law (GF := GF)) (hOpen : mvcc.api.etcdStorage_open.law (GF := GF))
    (hRest : mvcc.api.backendRest_open.law (GF := GF))
    (s ep ap sn : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai at0 dsi : w64) (nc : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk : Loc)
    (hi : uint.Z ai < uint.Z sv.Metadata'.Index')
    (d : mvcc.KBReal) (D : backend.Data) (lgh : Loc)
    (hkb : E.BkTie = srvBkTie d)
    (hdbo : storage.dbOpensOk) (hsop : storage.snapOpensOk)
    (hP : d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ ciKeys d.P ∧ storage.hooksParams d.P)
    (hcfgl : cfg.Logger' ≠ null) (hmmap : storage.openMmapOk cfg)
    (tI : w64) (hmeta : metaIs D (sv.Metadata'.Index', tI))
    (hSB : consistentIndex.SetBackend.spec (GF := GF) (hG := hG))
    (st : ApplyState) (b : GoInterface)
    (hle : uint.Z (ciEff γ st.k) ≤ uint.Z sv.Metadata'.Index')
    (hLR : lease.lessor.Recover.spec (GF := GF) (hG := hG))
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl (srvObjsOn al ast lp cl d.be))
    -- (P6.2, 2026-11-03, F9) a mode the server runs in, in place of `hoff`; `Recover` with auth on
    (hany : E.authMode ≠ .any)
    (hRecOn : E.authOn = true → authRecoverOn.spec (GF := GF) (hG := hG))
    -- (the lease-expiry plan's S2–S4, Probe 4, 2026-11-05) the image's lease records `recs`, which
    -- `Recover` restores at the mode `mono` (`Lr` their ids in the caller's order, `reqOf` their
    -- requests), the apply thread's halves of the live set at `L0` and of the ever set at `U`; in a
    -- cluster that grants none, no record, the revocable mode (until then the bucket empty)
    (mono : Bool) (recs : List (w64 × w64 × w64)) (U : List w64) (reqOf : w64 → w64)
    (Lr L0 : List w64)
    (hbe0 : backend.bktEnts (((backend.rbData d.P D).lookup go!"lease").getD ∅) =
      recs.map lease.leaseRecEnc)
    (hrmono : mono = true → ∀ id ∈ L0, id ∈ recs.map (·.1))
    (hrUL : mono = false → ∀ id ∈ recs.map (·.1), id ∈ U → id ∈ L0)
    (hmlg : mono = true → E.lg = true)
    (hreq : ∀ x ∈ recs, sint.Z (reqOf x.1) ≤ sint.Z x.2.1) (hperm : Lr.Perm (recs.map (·.1)))
    (hlgf : E.lg = false → recs = [] ∧ mono = false) (r0 : apply.RestM)
    -- (strict M1, 2026-11-06) the KV at the applied `A`'s model (`kvApplied`'s; the mvcc merge: by
    -- the auth mode), the image recording an unfinished compaction iff `u`. Until then the store's
    -- internals: the watch flag, `watchableStore.Restore` over the backend's own specs, the restored
    -- log `R`, its key image at the records `r`.
    (u : Bool) (hxA : x.log = kvModelM E.authOn γr.kv A ∧ x.crev = crevOf γr.kv A)
    (hbr : mvcc.bridgeParams d.P)
    (hGTP : EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hSTP : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (γp : WTNames) (hrbw : receiptBound GF ≤ backend.wbInit - 6)
    (hRel : storage.storage.Release.spec (GF := GF) (hG := hG))
    (stp : Loc) (γd γt : GName) (img : w64 → backend.Data → IProp GF) (nt : Nat)
    (hstp : storage.storageSnap stp ss) (hnt : nt ≤ uint.nat sv.Metadata'.Index')
    (hNAB : schema.NewAlarmBackend.spec (GF := GF) (hG := hG))
    (hAR : v3alarm.AlarmStore.Recover.spec (GF := GF) (hG := hG))
    (halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅)
    (halbi : d.P.has mvcc.alarmBI ∧
      d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI) (hlpw : mvcc.leaseParams d.P)
    (hNAuB : schema.NewAuthBackend.spec (GF := GF) (hG := hG))
    -- (P6.2, F9) the image's auth facts by the mode (off, `hauthb`), its log `A'`
    (A' : List EntryModel) (hauthI : snapAuthImgM E.authMode γr d.P D A A') (hAA' : A <+: A')
    -- (strict M1, 2026-11-06) the image's state reachable and short (`dbImage`'s `imageStOk`; the
    -- mvcc merge: the model by the mode)
    (hst : imageStOk (kvModelM E.authOn γr.kv A') (crevOf γr.kv A'))
    -- (strict M1's, kept by R4) the image's history attaches no lease to a key (`specSnapM`'s)
    (hnl : mvcc.LogNoLease (kvModelM E.authOn γr.kv A'))
    (hNMB : schema.NewMembershipBackend.spec (GF := GF) (hG := hG))
    (hCSB : membership.RaftCluster.SetBackend.spec (GF := GF) (hG := hG))
    (hmemb : ((backend.rbData d.P D).lookup go!"members").isSome ∧
      ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
      ((backend.rbData d.P D).lookup go!"cluster").isSome)
    (hClose : backend.backend.Close.spec (GF := GF) (hG := hG))
    (hCRec : membership.RaftCluster.Recover.spec (GF := GF) (hG := hG))
    (memI : GMap w64 apply.MemberM)
    (himg : membership.clusterImageOk cl (backend.rbData d.P D) memI)
    (hRAP : rafthttp.Transport.RemoveAllPeers.spec (GF := GF) (hG := hG))
    (hAP : rafthttp.Transport.AddPeer.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (dir : w64 → List GoString)
    (ps : List w64) (idm : w64)
    (hdir : γn.dir = dir) (hdok : netDirOk dir) (hps : ∀ f, dir f ≠ [] ↔ f ∈ ps)
    (hlid : c.lid = idm)
    (hNUA : EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG))
    (msi : w64) (cs0 : Loc) (fg : GoInterface) (quota : w64) (wad : time.Duration)
    (hbuq : apply.backendUnderQuota) (γnc : NotifyNames)
    -- (2026-11-01, J8a-5) the alarm store's `Get` with no alarm, after its `Recover`
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    -- (the lease-expiry plan's step 2) the range deleter's argument (the mvcc merge, 2026-11-06:
    -- `lean`'s `watchableStore.Write` and the compacting backend's safe-range specs dropped, the
    -- store's `Write` being `KV.Write.contract` at the handle's type, `shapes.law`)
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       isServerM E.authOn s γ ci TM E ρ γr ∗
       taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
       taNotifycAddr ap ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
       epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epDiskSnapAddr ep ↦ dsi ∗
       srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
       srvCfgAddr s ↦□ cfg ∗ structFieldRef EtcdServer go!"snapshotter" s ↦□ ss ∗
       structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
       snap.isSnapshotter ss ∗ backend.fileHolds (snap.snapDBPath ss sv.Metadata'.Index') D ∗
       backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
       (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
       storage.isBackendHooks hk
         ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩ lgh ∗
       applyThread γ st ∗ applyBackend γ ci b ∗
       srvApplyKVM E.authOn s E ρ.wait x (srvAuthAtLog γr.kv srvAuthSt0 A) ∗ E.RO r0 ∗
       apply.ltHalf E L0 ∗ apply.everOwn E U ∗
       -- (in the monotone mode, every id of `U` live: `ever_live_modeM`)
       □ (⌜mono = true → ∀ u ∈ U, u ∈ L0⌝ -∗
         [∗list] x ∈ recs, ⌜x.1 ∉ U⌝ ∨ lease.leaseReqIs (mvccLeases E.γ) x.1 (reqOf x.1)) ∗
       □ ([∗list] id ∈ recs.map (·.1), lease.leaseGranted (mvccLeases E.γ) id) ∗
       lease.lessorInv lp (mvccLeases E.γ) ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
       lease.lessorModeIs (mvccLeases E.γ) mono ∗
       -- (2026-11-04, the lease-expiry plan's step 2) the lessor's configuration (`minLeaseTTL`, for
       -- `Recover`'s TTLs)
       lease.lessorCfg lp ∗
       -- (strict M1, 2026-11-06) the KV the store's handle, mvcc's image of the image's model, its
       -- compaction revision's permit (until then the KV's closer, its close right now `mvccOpen E.γ`; the
       -- watchable store, `certOk`, the restored log's receipt, the permits at the records)
       srvKVAddr s ↦□ E.kv ∗
       mvcc.api.mvccImage D (kvModelM E.authOn γr.kv A') (crevOf γr.kv A') u ∗
       E.Cp (crevOf γr.kv A') ∗
       □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗ srvWTPool E γp ∗
       rnStorageAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.storage.storage.ty) #stp : GoInterface) ∗
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
       srvStopChans γ d ∗ backend.bOpen d.γB (srvOpenQ E.authMode) ∗
       -- (2026-11-02, the backend-auth-split stage) the apply thread's token, for the pooled
       -- readers of the new backend (the alarm store's, the auth store's and the cluster's
       -- `Recover`) and (strict M1) the store's `Restore`, given back
       threadTok ∗
       snapAuthResM E.authMode s ast E.RD γr A' ∗ srvRLogLb γr.raft A' ∗
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
    {{ RET #(); snapWalkPost s ep sv γ ci E ρ γr d D A A' x ss (config.backendPathOf cfg.DataDir') hk γt γn t c rs idm lp al ast cl memI
        quota wad Lr recs U reqOf ∗ notifyRcvN γnc 1 ∗ threadTok }} := by
  wp_start as ⟨#Hsrv, #Hsn, #Hsnap, #Hnc, #Hncb, Hrcv, Hai, Hat, Hdsi, Hlr, Hbr, #Hcfg, #Hssf, #Hhkf, #Hiss, Hfile, Hpath, #Hfg, #Hbh, Hst, Hab, HKV, HRS, HL0, HEv0, #HRqs, #HGrs, #Hlinv, #Hlpf, #Hlrev, #Hlcfg, #Hkvf, #Him, HCp, #HkSz, #HWP, #Hstpf, #Hsdinv, Hγt, #Half, #HisAl, #Haustf, #Hclf, #Hirc, #Htrf, Htlive, #Hmidf, #Hmembers, Hmsi, Hcs0, #Hfgf, #Hfgok, #Hqbf, #Hwadf, #HoSC, HoOh, HthT, HauR, #HA', #HmetaB⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨-, -, ⟨%sfv, #Hfl⟩, #Hatm, -⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, ⟨%gg, #Hgg, #Hggs⟩, -⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hpbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hsnap' := Hsnap
  iunfold ownSnapM at Hsnap'
  icases Hsnap' with ⟨%sds, %smp, %suf, %Hsnn, #HsD, #Hsd, #HsM, #Hsm, #Hspb⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hIES sn DFrac.discard (some sv) $$ [$Hrpkg] as %b ⟨%Hb, -⟩
  · simp only [snapOpt]; iexact Hsnap
  simp only [Option.elim] at Hb
  subst Hb
  have hne : sv.Metadata'.Index' ≠ W64 0 := by intro h; rw [h] at hi; word
  simp only [hne, decide_false]
  (try wp_auto)
  iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hggs
  icases Hggs with ⟨#HInc, #HDec, -⟩
  wp_apply HInc
  (try wp_auto)
  wp_apply hLg s sfv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  -- the "applying snapshot" log
  wp_apply hU64 as %fl1 -
  wp_apply hU64 as %fl2 -
  wp_apply hGI $$ [Hsm] as -
  · iframe #
  wp_apply hU64 as %fl3 -
  wp_apply hGT $$ [Hsm] as -
  · iframe #
  wp_apply hU64 as %fl4 -
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fl1, fl2, fl3, fl4]
  isplitr
  · ipureintro; rfl
  iintro %fsl1 ⟨-, -⟩
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  -- `if GetIndex() <= ep.appliedi { Panic }`: not taken
  wp_apply hGI $$ [Hsm] as -
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · exfalso; word
  (try wp_auto)
  -- `<-toApply.notifyc`: raft persisted the snapshot
  wp_apply wp_notify2_receive1 γnc nc iprop(True) iprop(True) $$ [Hrcv] as ⟨Hrcv, -⟩
  · iframe #; iexact Hrcv
  (try wp_auto)
  -- `s.bemu.Lock()`: `bemu`'s whole lock invariant
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold srvBemuReaderAt at Hbr
  wp_apply sync.RWMutex.wp_Lock $$ [$Hbr] as ⟨Hbl, Hbm⟩
  (try wp_auto)
  -- `OpenSnapshotBackend(s.Cfg, s.snapshotter, snapshot, s.beHooks)`: the snapshot's backend, its
  -- names announced (`snap_create`), the store's late registration slot fresh
  ihave #HsrvCI := Hsrv
  iunfold isServerM at HsrvCI
  icases HsrvCI with ⟨-, #HCI, -⟩
  iunfold isServerCI at HCI
  icases HCI with ⟨#Hcif, #Hisci, #Hinv⟩
  -- (strict M1) the store's registration and the write invariant the backend is opened at
  imod hWA with ⟨%gx', HwReg, HlateW⟩
  imod (ghostVar_alloc (GF := GF) sv.Metadata'.Index') with ⟨%γmt0, Hmt0⟩
  icases ghostVar_halves γmt0 _ $$ Hmt0 with ⟨Hmt0a, Hmt0b⟩
  imod (dghostVar_alloc (GF := GF) false) with ⟨%γwr0, Hwr0⟩
  imod (token_alloc (GF := GF)) with ⟨%γpd0, Hpd0⟩
  let π0 : ApplyPhys := ⟨γmt0, γwr0, γpd0, (sv.Metadata'.Index', tI), γmt0, γmt0⟩
  ihave Hcreate := snap_create γ π0 d.P D (mvcc.api.mvccW gx') hmeta hP.2.2.1 $$ HmetaB Hinv Hpd0 Hmt0a HlateW
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hschpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Hhooks := hooksOk_server_fut hOn hSave hPut hBUR hID hName hSafe γ π0 ci d.P
    (fun _ => mvcc.api.mvccW gx') hk lgh hP.2.2.1 hP.2.2.2 $$ [$Hspkg $Hbpkg $Hschpkg $Hcipkg $Hbh $Hisci $Hinv]
  -- (2026-11-06, `notes/begin-tok-plan.md`) `OpenSnapshotBackend`'s instance, from the server's bound
  ihave %Htb0 : ⌜threadBound GF ≤ backend.rdPoolN⌝ $$ [Hsrv]
  · iunfold isServerM at Hsrv
    icases Hsrv with ⟨-, -, -, -, -, -, %h⟩
    ipureintro; exact h
  haveI : ThreadBoundLe GF (2 ^ 29) := ⟨by unfold backend.rdPoolN at Htb0; omega⟩
  wp_apply hOSB cfg ss sn smp hk DFrac.discard DFrac.discard sv.Metadata' d.P D
      (fun _ => mvcc.api.mvccW gx') (fun γB => batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P))
      (snapOpenK γ π0 d.P) $$ [Hfile Hpath Hcreate]
    as %be %err ⟨-, -, Hres⟩
  · iframe #; iframe Hfile Hpath
    iunfold storage.openPre
    iframe Hfg Hhooks
    isplitr
    · ipureintro; exact ⟨hdbo, hmmap, hcfgl, hP.1, hP.2.1⟩
    iexact Hcreate
  icases Hres with (⟨%Herr, %nb, %γB, %Hbe, Hnew, #HhkAt, Hdbp, #HnFile⟩ | ⟨%Herr, -, -⟩)
  rotate_left
  · exfalso
    exact Herr.2.2 ⟨hsop.1 ss, hsop.2.1 _ _⟩
  subst Herr Hbe
  -- (2026-11-02, the backend-auth-split stage) the new backend's reader slots into its pool and the
  -- counted stock (`backend.newPostK_pool`), within the server's thread bound (`isServer`'s)
  ihave %Hrdb : ⌜threadBound GF ≤ backend.rdPoolN⌝ $$ [Hsrv]
  · iunfold isServerM at Hsrv
    icases Hsrv with ⟨-, -, -, -, -, -, %h⟩
    ipureintro; exact h
  imod backend.newPostK_pool Hrdb ⊤ _ _ _ _ _ _ _ $$ Hnew with Hnew
  -- (strict M1) the new backend's instance, compacting (the API's storage), at the old one's
  -- parameters
  obtain ⟨d', hγ', hbe', hgx', hP', hcm'⟩ : ∃ d' : mvcc.KBReal, d'.γB = γB ∧ d'.be = nb ∧
      d'.gx = gx' ∧ d'.P = d.P ∧ d'.cm = true :=
    ⟨{ d with γB := γB, be := nb, gx := gx', cm := true }, rfl, rfl, rfl, rfl, rfl⟩
  subst hγ' hbe' hgx'
  have hbr' : mvcc.bridgeParams d'.P := by rw [hP']; exact hbr
  -- the opener's `K` (the announcement's pieces) out of the post; the rest is the store's, at
  -- `K := True` (`etcdStorage_open.law`'s `newPostKP`)
  iunfold backend.newPostKP at Hnew
  icases Hnew with ⟨#HnB, #HnSC, HnK, HnV, HnH, HnRB, #HnPool, HnRT, HnDl, HnFk, HnSr⟩
  ihave Hnew : backend.newPostKP (GF := GF) d'.γB d.P (fun _ => mvcc.api.mvccW d'.gx)
      (fun γB => batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) (fun _ => iprop(True))
      d'.be D $$ [HnV HnH HnRB HnRT HnDl HnFk HnSr]
  · iunfold backend.newPostKP
    iframe HnB HnSC HnV HnH HnRB HnPool HnRT HnDl HnFk HnSr
  ihave #HhkAtN : backend.hooksAt d'.be (storage.hooksIface hk) $$ []
  · iexact HhkAt
  iunfold snapOpenK at HnK
  icases HnK with ⟨HnCls, #HmetaN, %jf, %γcf, Htcf, #Hidxf⟩
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  -- `s.consistIndex.SetBackend(newbe)`: the protocol moves to the snapshot's backend's names
  iunfold applyBackend at Hab
  icases Hab with ⟨Hown, #Hmb⟩
  ihave #Hcipkg' : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  let π' := futPhys π0 d'.γB
  let s' : ApplyState := ⟨W64 0, sv.Metadata'.Index', sv.Metadata'.Index', false⟩
  wp_apply (wp_ci_swap hSB γ ci st s' π' jf γcf b _ rfl rfl
      ⟨by simp [s', ciEff, π', π0], by simp [s', ciEff, π', π0]⟩ (by simpa [π', π0] using hle))
    $$ [Hst Hown Hmt0b Hwr0 Htcf] as ⟨Hst, #Hreg', Hfs, Hown⟩
  · iframe #; iframe Hst Hown Hmt0b Hwr0 Htcf
  -- the new backend's payment rights, back from the futures: its write-back tokens, its open
  -- token (the constructors' half, the pool's shares, the counted stock's shares)
  iunfold futStash at Hfs
  icases Hfs with ⟨Hnwb, Hnop⟩
  ihave Hnop1 : backend.bOpen (GF := GF) d'.γB 1 $$ [Hnop HnCls]
  · iunfold backend.bOpen; iframe Hnop HnCls
  icases (backend.bOpen_one_pool d'.γB).1 $$ Hnop1 with ⟨HnOh, HnOp, HnOs⟩
  ihave HnPl := backend.bkRPool_intro d'.γB d.P d'.be $$ [$HnPool $HnOp]
  -- (strict M1) the counted stock's open shares: the store's `rdStockN - 2`, and two for the
  -- server's long-lived readers (the apply thread's, the storage-version monitor's)
  icases (rdStock_split2 (backend.bOpen (GF := GF) d'.γB backend.rdOpen)).1 $$ HnOs
    with ⟨HnOs, HnOa, HnOm⟩
  -- the write-back tokens: two for the lessor's `Recover`, one for the hook's install, two for the
  -- alarm store's and the cluster's `Recover`, two for the store; the rest the new backend's stock
  ihave Hnwb : ownToks d'.γB.wb ((backend.wbInit - 2) + 2) $$ [Hnwb]
  · rw [show (backend.wbInit - 2) + 2 = backend.wbInit by unfold backend.wbInit; omega]
    iexact Hnwb
  icases ownToks_add_1 2 _ d'.γB.wb $$ Hnwb with ⟨Hnwb, Hwb2⟩
  icases toks_take d'.γB.wb _ 1 (by unfold backend.wbInit; omega) $$ Hnwb with ⟨Hnwb, Hwb1⟩
  icases toks_take d'.γB.wb _ 2 (by unfold backend.wbInit; omega) $$ Hnwb with ⟨Hnwb, Hwb2'⟩
  icases toks_take d'.γB.wb _ 1 (by unfold backend.wbInit; omega) $$ Hnwb with ⟨Hnwb, Hws1⟩
  icases toks_take d'.γB.wb _ 1 (by unfold backend.wbInit; omega) $$ Hnwb with ⟨Hnwb, Hws2⟩
  imod srvWTStock_alloc γp.cnt d' (backend.wbInit - 2 - 1 - 2 - 1 - 1) (by unfold backend.wbInit at hrbw ⊢; omega) ⊤ $$ [Hnwb] with #HnS
  · iexact Hnwb
  ihave #HnSup := wbSupply_of_stock E γp d' $$ [$HWP $HnS]
  -- (strict M1) the store's resources over the new backend (`etcdStorage_open.law`), at the
  -- image's committed log `A'`, and the client's rest (`backendRest_open.law`), with two counted
  -- slots for the server's readers
  ihave #HkSz' : □ (∀ (γ' : backend.BNames) (b' : Loc), mvcc.keySized (GF := GF) γ' d'.P b') $$ []
  · rw [hP']; iexact HkSz
  imod (hOpen d' (fun γB => batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P))
      (fun _ => iprop(True)) D (kvModelM E.authOn γr.kv A') (crevOf γr.kv A') u hbr' (by rw [hP']; exact hlpw) hcm')
    $$ [Hnew Hws1 Hws2 HwReg HnOs] with ⟨HsF, Hrest, Hrt1, Hrt2⟩
  · rw [hP']
    iframe HkSz Him Hnew HwReg HnOs HnSup
    iunfold backend.wbTok
    iframe Hws1 Hws2
  dsimp only at *
  ihave ⟨#HnSC', -, HnH, HnRB, #HnPool', HnRA⟩ := hRest d'.γB d'.P (fun _ => iprop(True)) d'.be D $$ Hrest
  ihave HrtA : apply.bkRT (GF := GF) d' $$ [Hrt1 HnOa]
  · iunfold apply.bkRT; iframe Hrt1 HnOa
  ihave HrtM : apply.bkRT (GF := GF) d' $$ [Hrt2 HnOm]
  · iunfold apply.bkRT; iframe Hrt2 HnOm
  -- the old backend's objects, from the rest resource
  -- (the lease-grant stage, 2.9; the lease-expiry plan's X2) a cluster that grants none
  rw [hRO]
  iunfold srvRestOwnH at HRS
  icases HRS with ⟨HoRO, HoObj⟩
  iunfold srvRestOwn at HoRO
  -- (P6.2) the old backend's buckets: nothing uses them after the install
  icases HoRO with ⟨-, -, HoMem, -⟩
  iunfold srvObjsOn at HoObj
  icases HoObj with ⟨HoAl, HoAu, HoLe, HoCl⟩
  -- the apply thread's KV resources (P6.2: by the mode, `srvApplyKVM_open`); (the lease-expiry
  -- plan's step 2) the lessor's range deleter, `Hrdat`
  -- (the mvcc merge) the row by the mode (`srvApplyKVM_open`)
  ihave HKV := (srvApplyKVM_open _ _ _ _ _ _).1 $$ HKV
  icases HKV with ⟨%ua, Hua, #Hufor, HaKV, Hbo, Hrev, Hauar, ⟨%w0, %RD0, #Hwf, #Hwok, HRD0⟩, Hrdat⟩
  ihave #Haus := applierFor_envAus ua E $$ Hufor
  iunfold apply.applyKV at HaKV
  icases HaKV with ⟨%up, %Hup, HuOwn, HkvOwn, HcO⟩
  iunfold apply.cmpOwn at HcO
  icases HcO with ⟨HmO, HcrO⟩
  iunfold apply.kvOwn at HkvOwn
  icases HkvOwn with ⟨⟨%c0, HwSt⟩, HkBk, HlLive, HERD⟩
  iunfold apply.kvBk at HkBk
  icases HkBk with ⟨%B0, HmB, -, HB0⟩
  rw [hkb]
  iunfold srvBkTie at HB0
  icases HB0 with %HB0
  subst B0
  ihave HwSt' := HwSt
  iunfold srvApi.wSt at HwSt'
  icases HwSt' with ⟨HwSt1, HwSt2⟩
  iunfold srvApi.crOwn at HcrO
  icombine HwSt2 HcrO gives %Hc0
  obtain ⟨-, Hc0⟩ := Hc0
  subst Hc0
  ihave HwSt : srvApi.wSt (GF := GF) E.γs x.log x.crev $$ [HwSt1 HwSt2]
  · iunfold srvApi.wSt; iframe HwSt1 HwSt2
  ihave HcrO : srvApi.crOwn (GF := GF) E.γs x.crev $$ [HcrO]
  · iunfold srvApi.crOwn; iexact HcrO
  iunfold apply.leasesLive at HlLive
  icases HlLive with ⟨%Ll, #HlK, HlUser, HlLt⟩
  -- (S2–S4, Probe 4) the two halves of the live set agree, and move to the records' ids
  imod ltHalf_agree_upd E Ll L0 Lr $$ HlLt HL0 with ⟨%HLeq, HLt1, HLt2⟩
  iunfold lease.lessorUser at HlUser
  icases HlUser with ⟨HlOwn, HlRd, HlRv⟩
  -- the store invariant and the store's handle (`isServer`'s `srvKVInvs`)
  ihave #Hsrv3 := Hsrv
  iunfold isServerM at Hsrv3
  icases Hsrv3 with ⟨-, -, -, #Hat3, -⟩
  iunfold srvAtomicsM at Hat3
  icases Hat3 with ⟨-, -, #Hkvi⟩
  ihave ⟨#HkS, %Hkm⟩ := srvKVInvsM_kvStoreInvW E.authOn s E γr $$ Hkvi
  rw [Hkm.1, Hkm.2]
  ihave #HkS' := HkS
  iunfold srvApi.kvStoreInvG at HkS'
  icases HkS' with ⟨#HisM, -⟩
  (try wp_auto)
  -- `s.lessor.Recover(newbe, …)`: the lessor on the new backend, no lease live
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  ihave #Hlspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  -- (the lease-expiry plan's S1) the range deleter's owner's half, for `Recover` to replace
  -- (the mvcc merge) `Hrdat` is `∃ rd, lease.rdOwn (mvccLeases E.γ) rd ∗ mvccDeleter rd E.γ`
  icases Hrdat with ⟨%rd0, Hro, -⟩
  have hmonoL : mono = true → ∀ id ∈ Ll, id ∈ recs.map (·.1) := by
    intro hm
    cases hl : E.lg
    · rw [(hlgf hl).2] at hm; cases hm
    · rw [HLeq hl]; exact hrmono hm
  imod ever_live_modeM E lp mono U Ll _ hmlg $$ [Hlinv Hlrev HEv0 HlOwn] with ⟨HEv0, HlOwn, %HUm⟩
  · iframe Hlinv Hlrev HEv0 HlOwn
  have hUL0 : mono = true → ∀ u ∈ U, u ∈ L0 := fun hm u hu => by
    rw [← HLeq (hmlg hm)]; exact HUm hm u hu
  ihave #HRqs := HRqs $$ %hUL0
  have hULL : ∀ id ∈ recs.map (·.1), id ∈ U → id ∈ Ll := by
    intro id hid hu
    cases hm : mono
    · cases hl : E.lg
      · rw [(hlgf hl).1] at hid; cases hid
      · rw [HLeq hl]; exact hrUL hm id hid hu
    · exact HUm hm id hu
  -- the ids the lessor ever had: handed over with a record (in a cluster that grants leases), kept
  -- otherwise
  ihave ⟨HEvR, HEvK⟩ : iprop((if recs = [] then iprop(True) else lease.leaseEver (mvccLeases E.γ) U) ∗
      (if recs = [] then apply.everOwn E U else iprop(True))) $$ [HEv0]
  · by_cases hrn : recs = []
    · rw [if_pos hrn, if_pos hrn]; iframe HEv0
    · rw [if_neg hrn, if_neg hrn]
      cases hl : E.lg
      · exact absurd (hlgf hl).1 hrn
      · isplitl
        · iapply apply.everOwn_of_lg E U hl $$ HEv0
        · itrivial
  wp_apply hLR lp (mvccLeases E.γ) d.be d' (mvcc.api.mvccW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) (1 : Qp).half
      (fun _ => True) (backend.rbData d.P D) _ rd0 Ll _ mono recs U reqOf Lr
      trivial (by rw [hP']; exact hlpw) hbe0 hmonoL hULL hreq hperm
    $$ [HoLe HlOwn HlRv HnOh Hwb2 HnRB Hro HEvR]
    as ⟨HnLe, HlOwn, HEvP, #HRq', HlRv, Hro, HnOh, HnRB, -⟩
  · -- (2026-11-02, the backend-auth-split stage) at every bucket (`rbOwn` is `rbPart ⊤`): the
    -- lessor, first on the new backend, gives its tracked buckets idle (`rbOwnIn ⊤`)
    iunfold backend.rbOwn at HnRB
    rw [hP']; iframe #; iframe HoLe HlOwn HlRv HnOh Hwb2 HnRB Hro HEvR
  ipersist s
  ihave HnRB : backend.rbOwnIn d'.γB (fun _ => True)
      ((backend.rbData d.P D).insert go!"lease" (((backend.rbData d.P D).lookup go!"lease").getD ∅))
      $$ [HnRB]
  · have hlk : ((backend.rbData d.P D).lookup go!"lease").getD ∅ =
        (Option.filter (fun _ => true) (D.lookup go!"lease")).getD ∅ := by
      rw [rbData_real_lookup d D go!"lease" (by decide)]
      cases D.lookup go!"lease" <;> rfl
    rw [hlk]
    iexact HnRB
  -- the image's lease bucket, kept (opaque from here: the later calls' posts would unfold it)
  generalize hlb : (((backend.rbData d.P D).lookup go!"lease").getD ∅) = lb
  ihave HEv : apply.everOwn E (U ++ recs.map (·.1)) $$ [HEvP HEvK]
  · by_cases hrn : recs = []
    · irevert HEvK
      simp only [if_pos hrn]
      rw [hrn, List.map_nil, List.append_nil]
      iintro H; iexact H
    · irevert HEvP; simp only [if_neg hrn]; iintro H
      cases hl : E.lg
      · exact absurd (hlgf hl).1 hrn
      · iapply apply.everOwn_to_lg _ _ hl $$ H
  -- the new range deleter, `s.kv.Write(traceutil.TODO())` (R4, 2026-11-07): `mvccDeleter` of the
  -- closure, from `KV.Write.contract` at the store handle's dynamic type (`shapes.law`) and `hTODO`
  -- (`lean`'s `lease.rdAt_intro` over `watchableStore.Write.spec`, until then)
  ihave Hrdat : iprop(∃ rd : GoFunc, lease.rdOwn (mvccLeases E.γ) rd ∗ mvcc.api.mvccDeleter rd E.γ) $$ [Hro]
  · haveI := Hp.1
    ihave %Hshd := hsh.1 E.kv E.γ $$ HisM
    obtain ⟨dty, dv, Hdeq, -, hWrC, -⟩ := Hshd
    ihave #HisMd : mvcc.api.isMvcc (interface.mkOk dty dv) E.γ $$ []
    · rw [← Hdeq]; iexact HisM
    iexists _
    iframe Hro
    iunfold mvcc.api.mvccDeleter
    isplitr
    · ipureintro; intro h; injection h with _ _ h3; cases h3
    iintro !> %q %B %Pw %Pre %Q %fw %R %Φ' !> ⟨Hmrd, HmBd, #Hhkd, Hpre, Hrund, HAUd⟩ HΦ'
    ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
    · iPkgInit
    ihave #Hmpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
    · iPkgInit
    rw [Hdeq]
    wp_auto
    wp_apply hTODO as %tr ⟨%Htrnn, Htr⟩
    (try wp_auto)
    wp_apply (hWrC E.γ tr true q B Pw Pre Q fw R)
      $$ [Hmrd Htr HmBd Hpre Hrund HAUd] as %tw ⟨-, HmBd, Htw, HQ⟩
    · iframe #; iframe Hmrd Htr HmBd Hpre Hrund HAUd
      ipureintro; exact Htrnn
    (try wp_auto)
    iapply HΦ'
    iframe HmBd HQ
    icases Htw with ⟨%σw, Htw, HR⟩
    iexists tr, σw
    iframe Htw HR
  (try wp_auto)
  -- `s.kv.Restore(newbe)`: the store over the image's history at the new backend
  -- (`KV.Restore.contract` at the store handle's dynamic type, at `restoreArgs_holds`'s
  -- precondition: no hook yet, no lease live)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  ihave #Hmvpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  -- (R4, 2026-11-07) the image's history attaches no lease to a key (`hnl`), so `KV.Restore` has no
  -- pending item: its `leaseOwn` at `Recover`'s live set `Lr`; the model by the mode
  have hpi : mvcc.pendItems (kvModelM E.authOn γr.kv A') [] = ∅ := by
    rw [mvcc.api.pendItems_nil]
    exact mvcc.leaseItemsOf_zero _ (mvcc.stateAfter_leaseZero _ hnl)
  have hit : ∀ it lid, (mvcc.pendItems (srvApi.stAt (kvModelM E.authOn γr.kv A')
      (crevOf γr.kv A')).log []).lookup it = some lid →
      lid ∈ Lr ∧ (it.Key'.length : Int) < 2 ^ 63 - 1 := by
    intro it lid h
    rw [srvApi.stAt_log, hpi] at h
    simp at h
  ihave Hrun : mvcc.api.hookRun (GF := GF)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) func.nil iprop(True)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) $$ []
  · unfold mvcc.api.hookRun
    rw [if_pos rfl]
    iintro ⟨H, -⟩; imodintro; iexact H
  ihave Hpost : iprop(batchLockInv (GF := GF) (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P) ={⊤}=∗
      batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P) ∗ True) $$ []
  · iintro H; imodintro; iframe H
  imod (srvKVInvsM_keysA E.authOn s E γr A') $$ Hkvi HA' with %Hkey
  ihave Hrp : srvApi.restorePreA (GF := GF) E.kv E.γ d d' (E.Pk d)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P))
      (srvApi.stAt (kvModelM E.authOn γr.kv A') (crevOf γr.kv A')) u Lr (DFrac.own (1 : Qp).half)
      func.nil iprop(True) (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P))
      iprop(True) iprop(True) iprop(True)
      (fun σ => iprop(⌜σ = srvApi.stAt x.log x.crev⌝ ∗
        srvApi.wSt E.γs (srvApi.stAt (kvModelM E.authOn γr.kv A') (crevOf γr.kv A')).log
          (srvApi.stAt (kvModelM E.authOn γr.kv A') (crevOf γr.kv A')).crev ∗
        srvApi.crOwn E.γs (srvApi.stAt (kvModelM E.authOn γr.kv A') (crevOf γr.kv A')).crev))
      $$ [HwSt HcrO HCp HmO HmB HsF HnH Hrun Hpost HlOwn]
  · iapply (srvApi.restoreArgs_holds Hp E.kv E.γ γr E.authOn E.γs x.log x.crev A A' d d' (E.Pk d)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) u Lr (DFrac.own (1 : Qp).half)
      func.nil iprop(True) (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P))
      iprop(True) hxA.1 hxA.2 hAA' hst.1 Hkey hit)
    simp only [srvApi.stAt_log, srvApi.stAt_crev, srvApi.kvStoreInv_eq]
    iframe HkS HwSt HcrO HA' HCp HmO HmB HsF HnH Hrun Hpost HlOwn
  iunfold srvApi.restorePreA at Hrp
  icases Hrp with ⟨-, HmO, HmB, HsF, %Hσ', HnH, HPre, Hrun, Hpost, HX, #Hreq, HlOwn, -, HAU⟩
  haveI := Hp.1
  ihave %Hsh := hsh.1 E.kv E.γ $$ HisM
  obtain ⟨kty, kvv, Hkveq, -, -, -, -, -, -, -, -, -, hRestC, -⟩ := Hsh
  ihave #HisM' : mvcc.api.isMvcc (interface.mkOk kty kvv) E.γ $$ []
  · rw [← Hkveq]; iexact HisM
  rw [Hkveq]
  simp only [interface.mkOk]
  (try wp_auto)
  have hR := (hRestC E.γ d d' (E.Pk d) (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P))
      (srvApi.stAt (kvModelM E.authOn γr.kv A') (crevOf γr.kv A')) u Lr (DFrac.own (1 : Qp).half)
      func.nil iprop(True) (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P))
      iprop(True) iprop(True) iprop(True)
      (fun σ => iprop(⌜σ = srvApi.stAt x.log x.crev⌝ ∗
        srvApi.wSt E.γs (srvApi.stAt (kvModelM E.authOn γr.kv A') (crevOf γr.kv A')).log
          (srvApi.stAt (kvModelM E.authOn γr.kv A') (crevOf γr.kv A')).crev ∗
        srvApi.crOwn E.γs (srvApi.stAt (kvModelM E.authOn γr.kv A') (crevOf γr.kv A')).crev)))
  rw [mvcc.api.etcdStorage_val] at hR
  simp only [interface.mkOk] at hR
  wp_apply hR
    $$ [HmO HmB HsF HnH HPre Hrun Hpost HX HlOwn HAU]
    as ⟨HmO, HmB, HoRest, HnH, -, HlOwn, %σ0, %Hσ0, HwSt, HcrO⟩
  · iframe #
    rw [mvcc.api.etcdStorage_hook, mvcc.api.etcdStorage_req]
    iframe HmO HmB HsF HnH HPre Hrun Hpost HX HlOwn
    isplitr
    · ipureintro; exact Hσ'
    isplitr
    · ipureintro; first | (left; rfl) | trivial
    isplitr
    · iexact Hreq
    isplitr
    · ipureintro; exact hit
    iunfold srvApi.auRestore at HAU
    iexact HAU
  simp only [mvcc.api.etcdStorage_hook, srvApi.stAt_log, srvApi.stAt_crev, hpi]
  (try wp_auto)
  -- the post-lock hook of the new names, installed on the new backend
  ihave #HCI' : isServerCI (GF := GF) s (γ.withPh π') ci $$ []
  · iunfold isServerCI; iframe Hcif Hisci
    rw [show consInv (GF := GF) (γ.withPh π') = consInv γ from rfl]
    iexact Hinv
  wp_apply hGTP s (γ.withPh π') ci (metaTM d'.γB d.P) $$ [$HCI'] as %g ⟨%Hgnn, #HhkS⟩
  wp_apply hSTP d'.γB d.P (mvcc.api.mvccW d'.gx) (batchLockInv (γ.withPh π') (metaTM d'.γB d.P)) d'.be
      (1 : Qp).half func.nil g $$ [HnOh HnH Hwb1] as ⟨HnOh, HnH⟩
  · iframe #; iframe HnOh HnH
    iunfold backend.wbTok; iexact Hwb1
  (try wp_auto)
  -- `s.consistIndex.ConsistentIndex()` (logged): read through the new backend's meta reads
  ihave #HmB' := HmetaN $$ %(mvcc.api.mvccW d'.gx) %d'.be HnB
  ihave Hab' : applyBackend (GF := GF) (γ.withPh π') ci
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #d'.be) $$ [Hown]
  · iunfold applyBackend; iframe Hown HmB'
  wp_apply (wp_ci_get hCIg (γ.withPh π') ci _ s' rfl) $$ [Hst Hab'] as ⟨Hst, Hab'⟩
  · iframe #; iframe Hst Hab'
    rw [show consInv (GF := GF) (γ.withPh π') = consInv γ from rfl]
    iexact Hinv
  wp_apply hU64 as %fl5 -
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fl5]
  isplitr
  · ipureintro; rfl
  iintro %fsl5 ⟨-, -⟩
  (try wp_auto)
  wp_apply (lc := 2) hInfo $$ []
  · ipureintro; exact Hlgnn
  -- `oldbe := s.be; s.be = newbe` under `bemu`'s write side (`srv_be_swap`)
  imod (lc_fupd_elim_later (E := ⊤) (P := bemuP s E.γbe 1)) $$ Hlc1 Hbm with Hbm
  ihave #HnRO : srvBeRO (GF := GF) d' $$ []
  · iunfold srvBeRO; iexists d'.gx, _; rw [hP']; iexact HnB
  imod srv_be_swap s E γp d' $$ HWP Hbm Hbo HnRO HnS HrtM Hlc2
    with ⟨%dold, %Hdold, Hbefull, ⟨%d2, %Hd2, HoMon⟩, HoAT, #HoRO, HoPl, Hbeback⟩
  (try wp_auto)
  icases Hbeback $$ Hbefull with ⟨Hbm, HbeA, HγbeA⟩
  wp_apply sync.RWMutex.wp_Unlock $$ [$Hbl Hbm] as Hbr
  · iframe #; inext; iexact Hbm
  (try wp_auto)
  -- `s.r.storage.Release(snapshot)`: the snapshot's index taken, the older files released
  imod (mono_nat_own_update (uint.nat sv.Metadata'.Index') (by word)) $$ Hγt with ⟨Hγt, #Htk⟩
  wp_apply hRel stp ss sn smp DFrac.discard DFrac.discard sv.Metadata' γd img (srvSnapRm γt γr) hstp
    $$ [] as %rerr ⟨-, -, %Hrerr⟩
  · iframe #
    iintro !> %j %hj
    iunfold srvSnapRm
    ileft
    iunfold snapTakenLb
    iapply monoNatLbOwn_le (uint.nat j) (by word) $$ Htk
  have hrerr : rerr = GoInterface.nil := by
    rcases Hrerr with h | h
    · exact h
    · exact absurd hsop.2.2.1 h
  subst hrerr
  (try wp_auto)
  -- `s.alarmStore.Recover(schema.NewAlarmBackend(lg, newbe))`: the alarm store on the new backend
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hNAB as %ab ⟨%abl, %Habl, #Hablg, #Hablb⟩
  subst Habl
  ihave #Halpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  icases toks_take d'.γB.wb 2 1 (by omega) $$ Hwb2' with ⟨Hwb2', Hwba⟩
  ihave HnRB := backend.rbOwnIn_part (GF := GF) _ (fun _ => True) _ $$ HnRB
  wp_apply hAR al d.be abl sfv.lg d'.be d'.γB d.P (mvcc.api.mvccW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) (1 : Qp).half
      (fun _ => True) ((backend.rbData d.P D).insert go!"lease" lb) trivial
      (by simp [mvcc.KBReal.P, mvcc.restBuckets]) halbi.1
    $$ [HoAl HnOh Hwba HnRB HnPl HthT]
    as %aerr ⟨%Haerr, HnAl, HnOh, HnPl, HthT, HnRB⟩
  · iframe #; iframe HoAl HnOh HnRB HnPl HthT
    isplitr
    · ipureintro; exact Hlgnn
    isplitl [Hwba]
    · iunfold backend.wbTok; iexact Hwba
    ipureintro
    rw [GMap.lookup_insert_ne _ _ (by decide)]
    exact halarm
  subst Haerr
  (try wp_auto)
  -- `s.authStore.Recover(schema.NewAuthBackend(lg, newbe))` (the named premise)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hNAuB as %aub ⟨%aubl, %Haubl, #Haublg, #Haublb⟩
  subst Haubl
  -- (the mvcc merge) the apply thread's reader token of the new backend is `apply.bkRT d'` (the open
  -- law's, strict M1); `lean`'s `writerOwn_rt` (mvcc's internal) dropped
  -- (P6.2, 2026-11-03, F9) `Recover` by the mode (`wp_authRecoverM`): off, `authRecoverOk`; on,
  -- the glue: the apply thread's auth row moves to the new backend, the new backend's idle auth
  -- buckets, auth reader slots and a quarter of its open token go to the realization, the old
  -- backend's quarter comes back
  ihave #Habl : ablOn (GF := GF) aubl d'.be sfv.lg $$ []
  · iunfold ablOn; iframe Haublb Haublg
  ihave #Hapkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  imod (backend.plHook_persist (GF := GF) d'.γB g) $$ HnH with #HplRO
  wp_apply (wp_authRecoverM s ast aubl sfv.lg E γr ua A A' d d' (mvcc.api.mvccW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) g
      (((backend.rbData d.P D).insert go!"lease" lb).insert go!"alarm" ∅) hkb hany
      (snapAuthImgR_of _ γr d.P D A A' hauthI) hAA' (by rw [hP']; exact halbi.2) Hlgnn Hgnn hRecOn)
    $$ [HauR HoAu Hauar HnOh HnPl HthT HnRB HnRA HoOh]
    as ⟨HnAu, HnOh, HnPl, HthT, HnRB, HoOh, Hauar⟩
  · rw [hP']; iframe #; iframe HauR HoAu Hauar HnOh HnPl HthT HnRB HoOh
    iunfold authRdSlots; rw [hP']; iexact HnRA
  ihave HnPl : backend.bkRPool (GF := GF) d'.γB d.P d'.be $$ [HnPl]
  · rw [← hP']; iexact HnPl
  (try wp_auto)
  -- `s.cluster.SetBackend(schema.NewMembershipBackend(lg, newbe))`
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hNMB as %mbl ⟨#Hmblg, #Hmblb⟩
  icases toks_take d'.γB.wb 1 1 (by omega) $$ Hwb2' with ⟨-, Hwbm⟩
  ihave #Hmempkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  wp_apply hCSB cl d.be mbl sfv.lg d' (mvcc.api.mvccW d'.gx) (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P))
      (srvOpenQ E.authMode) (snapKeepS E.authMode)
      ((((backend.rbData d.P D).insert go!"lease" lb).insert go!"alarm" ∅))
      (fun n h => snapKeepS_cluster _ n h)
    $$ [HoCl HnOh Hwbm HnRB] as ⟨HnCl, HnOh, HnRB⟩
  · -- (2026-11-02, the backend-auth-split stage; P6.2) at the kept buckets, given back idle
    ihave HnRB := backend.rbOwnIn_part (GF := GF) _ (snapKeepS E.authMode) _ $$ HnRB
    rw [hP']; (try rw [hgx']); iframe #; iframe HoCl HnOh HnRB
    isplitr
    · ipureintro; exact Hlgnn
    isplitl [Hwbm]
    · iunfold backend.wbTok; iexact Hwbm
    ipureintro
    refine ⟨?_, ?_, ?_⟩ <;>
      rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide)]
    · exact hmemb.1
    · exact hmemb.2.1
    · exact hmemb.2.2
  (try wp_auto)
  -- `go func() { … oldbe.Close() … }()`: the old backend closed, every share of its open token back
  imod ((typedPointsto_dfractional (GF := GF) lg_ptr sfv.lg).dfractional_persist (DFrac.own 1))
    $$ lg with #Hlgp
  have hdd : dold = d := (srvBkTie_inj d dold (hkb.symm.trans Hdold)).symm
  subst dold
  -- (strict M1) the old backend's open token, whole: the constructors' half, the pool's shares,
  -- the store's (`storageRest`, `Restore`'s) and the server's two readers'
  iunfold apply.bkRT at HoAT
  icases HoAT with ⟨-, HoS1⟩
  iunfold apply.bkRT at HoMon
  icases HoMon with ⟨-, HoS2⟩
  have hd2 : d2.γB = d.γB := congrArg Prod.fst Hd2
  rw [hd2, mvcc.api.etcdStorage_rest]
  -- (the backend-auth-split stage) with the old backend's pool's shares
  iunfold backend.bkRPool at HoPl
  icases HoPl with ⟨-, HoPs⟩
  ihave HoO1 : backend.bOpen (GF := GF) d.γB 1 $$ [HoOh HoPs HoRest HoS1 HoS2]
  · iapply (backend.bOpen_one_pool d.γB).2
    iframe HoOh HoPs
    iapply (rdStock_split2 _).2
    iframe
  iunfold srvBeRO at HoRO
  icases HoRO with ⟨%gxo, %Pko, #HoB⟩
  wp_apply wp_fork $$ [oldbe HoO1]
  · wp_apply wp_with_defer as %defer2 defer2
    (try wp_auto)
    wp_apply hInfo $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    -- (R2b-3c part 2) the old backend with its stop channels, at their client resources
    iunfold srvStopChans at HoSC
    icases HoSC with ⟨#HbC, #HsC⟩
    wp_apply hClose d.γB d.P (mvcc.api.mvccW d.gx) (batchLockInv γ (metaTM d.γB d.P)) d.be
      iprop(True) iprop(True) $$ [HoO1] as %cerr ⟨-, Hcerr⟩
    · iframe #; iframe HoO1
      isplitr
      · itrivial
      iapply backend.commitReq_true
    -- (R2b-3c) the old backend's file and what its stopped lock held, given back by `Close`,
    -- dropped (the snapshot's replaces it)
    icases Hcerr with ⟨%Dc, -, (⟨%h, -⟩ | %h)⟩
    rotate_left
    · exact absurd hsop.2.2.2 h
    have hcerr : cerr = GoInterface.nil := h
    subst hcerr
    (try wp_auto)
    wp_apply hInfo $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    ipureintro; trivial
  (try wp_auto)
  -- `s.cluster.Recover(api.UpdateCapability)`: the image's members
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  ihave #Hapipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api $$ []
  · iPkgInit
  have himg' : membership.clusterImageOk cl
      ((((backend.rbData d.P D).insert go!"lease" lb).insert go!"alarm" ∅)) memI := by
    unfold membership.clusterImageOk at himg ⊢
    rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
      GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
      GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide)]
    exact himg
  -- (2026-11-02, the backend-auth-split stage) the cluster's buckets idle, for its read
  icases (rbOwnIn_keep_split (GF := GF) E.authMode d'.γB _).1 $$ HnRB
    with ⟨HnRC, HnRB⟩
  ihave HnRB := backend.rbOwnIn_part (GF := GF) _ _ _ $$ HnRB
  wp_apply hCRec cl d' (mvcc.api.mvccW d'.gx) (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P))
      ((((backend.rbData d.P D).insert go!"lease" lb).insert go!"alarm" ∅)) _ memI himg'
    $$ [HnCl HnPl HthT HnRC HoMem] as ⟨HnCl, HnPl, HthT, HnRC, HnMem⟩
  · rw [hP']; (try rw [hgx']); iframe #; iframe HnCl HnPl HthT HnRC HoMem
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  -- `s.r.transport.RemoveAllPeers()`
  ihave #Hrhpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
  · iPkgInit
  -- (J8a-6, 2026-11-01) no `R`s come back, nor do the `AddPeer`s below take any: the peers borrow
  -- from the transport's pool (until J8a-7, 2026-11-01, the peers' no-remote facts went back to
  -- the transport, D22 J-T)
  wp_apply hRAP γn t c rs $$ [Htlive] as Htlive
  · iframe #; iframe
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  -- `for _, m := range s.cluster.Members() { … s.r.transport.AddPeer(m.ID, m.PeerURLs) }`
  iunfold srvMembersDir at Hmembers
  wp_apply Hmembers as %msl %mps %Hmps Hmsl Hmso
  (try wp_auto)
  ihave %Hmsll := ownSlice_len _ _ _ $$ Hmsl
  simp only [List.length_map] at Hmsll
  ihave IH2 : iprop(∃ (n : w64) (mm : Loc) (L : List w64), "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mm ∗
      "#s" ∷ s_ptr ↦□ s ∗
      "Htlive" ∷ trLive γn t c L ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z msl.len ∧ L.length ≤ (sint.Z n).toNat⌝ ∗
      "%Hcov" ∷ ⌜∀ (k : Nat) (p : Loc × w64), k < (sint.Z n).toNat → mps[k]? = some p →
        p.2 ≠ idm → p.2 ∈ L⌝) $$ [i m s Htlive]
  · iexists W64 0, _, []
    iframe i m s Htlive
    ipureintro
    refine ⟨⟨by decide, by have := Hmsll.2; word, by simp⟩, fun k p hk _ _ => ?_⟩
    exact absurd hk (by simp)
  iapply wp_fupd
  wp_join (iprop(∃ (L : List w64), "#s" ∷ s_ptr ↦□ s ∗
      "Hmsl" ∷ msl ↦* List.map Prod.fst mps ∗
      "Hmso" ∷ ([∗list] p ∈ mps, memberDirIs (GF := GF) dir p.fst p.snd) ∗
      "Htlive" ∷ trLive γn t c L ∗
      "%Hcov" ∷ ⌜∀ f, (netRh γn).member f → f ≠ idm → f ∈ L⌝))
    at (App (App (App (Val doFor) _) _) _) with [Hmsl Hmso IH2]
    as ⟨%L, #s, Hmsl, Hmso, Htlive, %Hcov⟩
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
      wp_apply hMID s idm $$ []
      · iframe #
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
        wp_for_post
        iframe
        iexists n + W64 1, _, L
        iframe
        iframe s
        ipureintro
        refine ⟨⟨by word, by word, by omega⟩, ?_⟩
        rw [Hn1]
        exact membersCov_step mps _ L L _ px Hpx Hcov (fun _ h => h) (fun h => absurd rfl h)
      · have Hpid : px.2 ≠ idm := by simpa using Hif
        obtain ⟨Hne, Hpl, Hown, Hpm⟩ :=
          addPeer_dir γn dir hdir hdok ps hps px.2 Hpxps mpus Hmok.2
        wp_apply (hAP γn t c L px.2 mpu (DFrac.own 1) mpus Hne Hpl Hown
            (by rw [hlid]; exact fun h => Hpid h.symm) Hpm) $$ [Htlive Hmpus]
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
        iframe s
        ipureintro
        refine ⟨⟨by word, by word, by simp only [List.length_append, List.length_singleton]; omega⟩, ?_⟩
        rw [Hn1]
        exact membersCov_step mps idm L (L ++ [px.2]) _ px Hpx Hcov
          (fun x hx => List.mem_append_left _ hx) (fun _ => List.mem_append_right _ (by simp))
    · wp_join_done
      iexists L
      iframe
      iframe s
      ipureintro
      exact membersCov_done γn dir hdir ps hps mps Hmps idm L (sint.Z n).toNat
        (by have h1 : mps.length = (sint.Z msl.len).toNat := Hmsll.1; omega) Hcov
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  -- the progress at the snapshot
  wp_apply hGT $$ [Hsm] as -
  · iframe #
  (try wp_auto)
  wp_apply hGI $$ [Hsm] as -
  · iframe #
  (try wp_auto)
  ihave #Hsm0 := Hsm
  iunfold smOpt at Hsm
  icases Hsm with (%Hsmnil | Hsmp)
  · exfalso; rw [Hsmnil.2] at hi; simp at hi
  iunfold smPts at Hsmp
  icases Hsmp with ⟨%spc, %spi, %spt, %suf2, %Hsmnn, #HsC, #Hsc, -⟩
  iunfold epConfState at Hcs0
  icases Hcs0 with ⟨Hcs0, -⟩
  (try wp_auto)
  -- `s.uberApply = s.NewUberApplier()`
  -- (2026-11-01, J8a-5) the store recovered has no alarm: `Get` returns none (`alarmEmpty`)
  ihave #HalG := alarmGetIs_empty hAG al d'.be $$ [$Halpkg $HisAl]
  wp_apply hNUA s sfv.lg al cl _ _ _ _ _ fg quota wad (DFrac.own (1 : Qp).half)
      (alarmEmpty al d'.be) true hbuq
    $$ [HbeA HnAl] as %ua' ⟨HbeA, HnAl, %up', %opts', %Hua', %Hopts', Hube⟩
  · iframe #; iframe HbeA HnAl
  ihave HnAl := alarmEmpty_beOn al d'.be $$ HnAl
  ihave Hube : iprop(∀ E1 : apply.AEnv GF, apply.backendOptsOk E1 opts' -∗
      apply.uberIs E1 up' opts' ∗ apply.uberOwn E1 up' (apply.alarmChain E1.authOn false false))
      $$ [Hube]
  · iintro %E1 Hbo
    icases Hube $$ %E1 Hbo with ⟨Hu, %ns, %cr, %hz, Ho⟩
    obtain ⟨rfl, rfl⟩ := hz trivial
    iframe Hu Ho
  (try wp_auto)
  -- the deferred "applied snapshot" log and the gauge's `Dec`
  wp_apply hU64 as %fd1 -
  wp_apply hU64 as %fd2 -
  wp_apply hGI $$ [Hsm0] as -
  · iframe #
  wp_apply hU64 as %fd3 -
  wp_apply hGT $$ [Hsm0] as -
  · iframe #
  wp_apply hU64 as %fd4 -
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fd1, fd2, fd3, fd4]
  isplitr
  · ipureintro; rfl
  iintro %fsld ⟨-, -⟩
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply HDec
  (try wp_auto)
  subst Hua'
  imodintro
  wp_pures
  iapply HΦ
  iframe Hrcv HthT
  ihave HnPl : backend.bkRPool (GF := GF) d'.γB d'.P d'.be $$ [HnPl]
  · rw [hP']; iexact HnPl
  ihave #HnB2 : backend.isBackend (GF := GF) d'.γB d'.P (mvcc.api.mvccW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) d'.be $$ []
  · rw [hP']; iexact HnB
  ihave #HnSz2 : mvcc.keySized (GF := GF) d'.γB d'.P d'.be $$ []
  · iapply HkSz'
  -- (R2b-3d) the new backend's file at the backend path (`OpenSnapshotBackend`'s)
  ihave #HnFile' : backend.bFile (GF := GF) d'.γB (config.backendPathOf cfg.DataDir') $$ []
  · iexact HnFile
  -- (R2b-3c part 2) the new backend with its stop channels
  ihave #HnSCE : backend.isStopChans (GF := GF) d'.γB d'.P (mvcc.api.mvccW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) d'.be $$ []
  · rw [hP']; iexact HnSC
  iunfold snapWalkPost
  rw [hlb]
  iexists d', π0, g, up', opts', L, spc, jf, γcf, w0, RD0, up, sfv.lg, ua
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3⟩ := Hopts'
    exact ⟨hP', hcm', rfl, hbr', Hcov, Hgnn, h1, h2.trans Hkveq.symm, h3⟩
  iunfold srvBemuReaderAt
  iframe
  iframe #

end proof
end EtcdGrove
end Perennial
