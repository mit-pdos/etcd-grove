/-
**`applySnapshot`'s code past the empty case** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`): `applySnapshot_walk`, the walk through the code from the spec's
premises to `snapWalkPost` (`SnapApplyDefs.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs

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
set_option maxHeartbeats 4000000 in
/-- **`applySnapshot`'s code, past the empty case** (S8d): from its premises to `snapWalkPost`. -/
theorem applySnapshot_walk
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
    (s ep ap sn : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai at0 dsi : w64) (nc : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk : Loc)
    (hi : uint.Z ai < uint.Z sv.Metadata'.Index')
    (d : mvcc.KBReal) (D : backend.Data) (lgh : Loc)
    (hkb : E.γ.kb = some d) (hcm : d.cm = false)
    (hdbo : storage.dbOpensOk) (hsop : storage.snapOpensOk)
    (hP : d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ ciKeys d.P ∧ storage.hooksParams d.P)
    (hcfgl : cfg.Logger' ≠ null) (hmmap : storage.openMmapOk cfg)
    (tI : w64) (hmeta : metaIs D (sv.Metadata'.Index', tI))
    (hSB : consistentIndex.SetBackend.spec (GF := GF) (hG := hG))
    (st : ApplyState) (b : GoInterface)
    (hle : uint.Z (ciEff γ st.k) ≤ uint.Z sv.Metadata'.Index')
    (hLR : lease.lessor.Recover.spec (GF := GF) (hG := hG))
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (hRO : E.RO = srvRestOwnH d.γB cl (srvObjsOn al ast lp cl d.be))
    (hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅)
    (hwq : E.γ.watchQ = true)
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
    (R : mvcc.Log) (hpre : x.log <+: [[], []] ++ R) (hRok : mvcc.restoreLogOk R)
    (hkI : mvcc.keyImage ([[], []] ++ R) D) (hbr : mvcc.bridgeParams d.P)
    (hGTP : EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hSTP : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (γp : GName) (hrbw : receiptBound GF ≤ backend.wbInit - 6)
    (hRel : storage.storage.Release.spec (GF := GF) (hG := hG))
    (stp : Loc) (γd γt : GName) (img : w64 → backend.Data → IProp GF) (nt : Nat)
    (hstp : storage.storageSnap stp ss) (hnt : nt ≤ uint.nat ai)
    (hNAB : schema.NewAlarmBackend.spec (GF := GF) (hG := hG))
    (hAR : v3alarm.AlarmStore.Recover.spec (GF := GF) (hG := hG))
    (halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅)
    (hNAuB : schema.NewAuthBackend.spec (GF := GF) (hG := hG))
    (hauthb : ((backend.rbData d.P D).lookup go!"auth").getD ∅ = authBoot ∧
      ((backend.rbData d.P D).lookup go!"authUsers").getD ∅ = ∅ ∧
      ((backend.rbData d.P D).lookup go!"authRoles").getD ∅ = ∅)
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
    (Tal : IProp GF) (zal : Bool) (hbuq : apply.backendUnderQuota) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       isServer s γ ci TM E ρ γr ∗
       taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
       taNotifycAddr ap ↦□ nc ∗ isUnitBag nc ∗
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
       srvApplyKV s E ρ.wait x ∗ srvRest E γr A ∗
       lease.lessorInv lp E.γ.leases ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
       srvKVCloser s E ∗
       (∃ (wsl : Loc) (γw0 : mvcc.WsNames), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
        mvcc.isWatchableStore wsl E.s γw0) ∗
       mvcc.certOk E.γ ([[], []] ++ R) ∗
       □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗ srvWTPool E γp ∗
       rnStorageAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.storage.storage.ty) #stp : GoInterface) ∗
       inv snapDirN (snapDirInv ss γd img (snapTakenLb γt)) ∗ monoNatAuthOwn γt 1 nt ∗
       srvAlarmStoreAddr s ↦□ al ∗ isAlarmStore al ∗
       srvAuthStoreAddr s ↦□ auth.authIface ast ∗ srvClusterAddr s ↦□ cl ∗
       membership.isRaftCluster cl ∗
       rnTransportAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t : GoInterface) ∗
       (trLive γn t c rs ∗ trPeersNoRem c rs) ∗ srvMemberIDAddr s ↦□ idm ∗
       ([∗list] _x ∈ List.replicate (8 * ps.length) (), c.R) ∗
       srvMembersDir cl ps dir ∗
       epMemSnapAddr ep ↦ msi ∗ epConfState ep cs0 ∗
       srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg ∗
       srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ quota ∗
       srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ wad ∗
       apply.alarmGetIs al Tal zal ∗ Tal ∗
       backend.isStopChans d.γB d.be ∗ backend.bOpen d.γB (1 : Qp).half ∗
       authRecoverOk ast ∗
       □ (∀ (π : ApplyPhys) (b : Loc), ⌜π.m0 = (sv.Metadata'.Index', tI)⌝ →
          isMetaBackend (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN) (readView (γ.withPh π))) }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applySnapshot")) (Val #ep))
        (Val #ap))
    {{ RET #(); snapWalkPost s ep sv γ ci E ρ γr d D A x R ss hk γt γn t c rs idm lp al ast cl memI
        quota wad Tal zal }} := by
  wp_start as ⟨#Hsrv, #Hsn, #Hsnap, #Hnc, #Hncb, Hai, Hat, Hdsi, Hlr, Hbr, #Hcfg, #Hssf, #Hhkf, #Hiss, Hfile, Hpath, #Hfg, #Hbh, Hst, Hab, HKV, HRS, #Hlinv, #Hlpf, Hkvc, ⟨%wsl, %γw0, #Hkvf, #Hwsl⟩, #Hcok, #HkSz, #HWP, #Hstpf, #Hsdinv, Hγt, #Half, #HisAl, #Haustf, #Hclf, #Hirc, #Htrf, Htlive, #Hmidf, HR8s, #Hmembers, Hmsi, Hcs0, #Hfgf, #Hfgok, #Hqbf, #Hwadf, #HalG, HTal, #HoSC, HoOh, #HauR, #HmetaB⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨-, -, ⟨%sfv, #Hfl⟩, -, -⟩
  iunfold srvFieldsAt at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, ⟨%gg, #Hgg, #Hggs⟩⟩
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
  iunfold isUnitBag at Hncb
  icases Hncb with ⟨%γnc, #Hncb'⟩
  wp_apply wp_bag_receive γnc nc (fun _ => iprop(True)) $$ [] as %u -
  · iexact Hncb'
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
  iunfold isServer at HsrvCI
  icases HsrvCI with ⟨-, #HCI, -⟩
  iunfold isServerCI at HCI
  icases HCI with ⟨#Hcif, #Hisci, #Hinv⟩
  imod (dghostVar_alloc (GF := GF) (none : Option (Loc × mvcc.StoreNames))) with ⟨%gx', Hgx⟩
  icases (dghostVar_split (GF := GF) gx' (none : Option (Loc × mvcc.StoreNames))
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)) $$ [Hgx] with ⟨HlateW, HlateR⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hgx
  ihave HlateW : mvcc.lateW (GF := GF) gx' $$ [HlateW]
  · iunfold mvcc.lateW; ileft; iexact HlateW
  imod (ghostVar_alloc (GF := GF) sv.Metadata'.Index') with ⟨%γmt0, Hmt0⟩
  icases ghostVar_halves γmt0 _ $$ Hmt0 with ⟨Hmt0a, Hmt0b⟩
  imod (ghostVar_alloc (GF := GF) false) with ⟨%γwr0, Hwr0⟩
  imod (token_alloc (GF := GF)) with ⟨%γpd0, Hpd0⟩
  let π0 : ApplyPhys := ⟨γmt0, γwr0, γpd0, (sv.Metadata'.Index', tI), γmt0, γmt0⟩
  ihave Hcreate := snap_create γ π0 d.P D gx' hmeta $$ Hinv Hpd0 Hmt0a HlateW
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hschpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Hhooks := hooksOk_server_fut hOn hSave hPut hBUR hID hName hSafe γ π0 ci d.P
    (fun _ => mvcc.lateW gx') hk lgh hP.2.2.1 hP.2.2.2 $$ [$Hspkg $Hbpkg $Hschpkg $Hcipkg $Hbh $Hisci $Hinv]
  wp_apply hOSB cfg ss sn smp hk DFrac.discard DFrac.discard sv.Metadata' d.P D
      (fun _ => mvcc.lateW gx') (fun γB => batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P))
      (snapOpenK γ π0) $$ [Hfile Hpath Hcreate]
    as %be %err ⟨-, -, Hres⟩
  · iframe #; iframe Hfile Hpath
    iunfold storage.openPre
    iframe Hfg Hhooks
    isplitr
    · ipureintro; exact ⟨hdbo, hmmap, hcfgl, hP.1, hP.2.1⟩
    iexact Hcreate
  icases Hres with (⟨%Herr, %nb, %γB, %Hbe, Hnew, Hdbp⟩ | ⟨%Herr, -, -⟩)
  rotate_left
  · exfalso
    exact Herr.2.2 ⟨hsop.1 ss, hsop.2.1 _ _⟩
  subst Herr Hbe
  iunfold backend.newPostK at Hnew
  simp only
  -- (the backend-compaction stage) the new backend never compacts (no compaction with a restore):
  -- its creator fixes nothing deletable
  icases Hnew with ⟨#HnB, #HnSC, HnK, HnV, HnH, HnRB, HnRT, Hdl, Hncmp, -⟩
  imod backend.dlNoDel_fix _ $$ Hdl with #Hnd
  -- (question 5's core stage, part (1)) the new backend's instance does not compact (no restore in
  -- compaction mode: Q5-3)
  obtain ⟨d', hγ', hbe', hgx', hP', hcm'⟩ : ∃ d' : mvcc.KBReal, d'.γB = γB ∧ d'.be = nb ∧
      d'.gx = gx' ∧ d'.P = d.P ∧ d'.cm = false :=
    ⟨{ d with γB := γB, be := nb, gx := gx', cm := false }, rfl, rfl, rfl, rfl, rfl⟩
  rw [← hbe']
  iunfold snapOpenK at HnK
  icases HnK with ⟨HnCls, %jf, %γcf, Htcf, #Hidxf⟩
  (try wp_auto)
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  -- `s.consistIndex.SetBackend(newbe)`: the protocol moves to the snapshot's backend's names
  iunfold applyBackend at Hab
  icases Hab with ⟨Hown, #Hmb⟩
  ihave #Hcipkg' : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  let π' := futPhys π0 γB
  let s' : ApplyState := ⟨W64 0, sv.Metadata'.Index', sv.Metadata'.Index', false⟩
  wp_apply (wp_ci_swap hSB γ ci st s' π' jf γcf b _ rfl rfl
      ⟨by simp [s', ciEff, π', π0], by simp [s', ciEff, π', π0]⟩ (by simpa [π', π0] using hle))
    $$ [Hst Hown Hmt0b Hwr0 Htcf] as ⟨Hst, #Hreg', Hfs, Hown⟩
  · iframe #; iframe Hst Hown Hmt0b Hwr0 Htcf
  -- the new backend's payment rights, back from the futures: its write-back tokens, its open
  -- token (the constructors' half and the readers' shares)
  iunfold futStash at Hfs
  icases Hfs with ⟨Hnwb, Hnop⟩
  ihave Hnop1 : backend.bOpen (GF := GF) γB 1 $$ [Hnop HnCls]
  · iunfold backend.bOpen; iframe Hnop HnCls
  icases (backend.bOpen_one_shares γB).1 $$ Hnop1 with ⟨HnOh, HnOs⟩
  ihave HnRTx := bkRTx_of_rdToks γB d.P d'.be _ $$ [$HnRT $HnOs]
  -- the old backend's objects, from the rest resource
  iunfold srvRest at HRS
  rw [hRO]
  iunfold srvRestOwnH at HRS
  icases HRS with ⟨HoRO, HoObj⟩
  iunfold srvRestOwn at HoRO
  icases HoRO with ⟨HoRB, HoMem⟩
  iunfold srvObjsOn at HoObj
  icases HoObj with ⟨HoAl, HoAu, HoLe, HoCl⟩
  -- the apply thread's KV resources
  iunfold srvApplyKV at HKV
  icases HKV with ⟨%ua, Hua, #Hufor, HaKV, Hbo, Hrev, Hauar, %w0, %RD0, #Hwf, #Hwok, HRD0⟩
  iunfold apply.applyKV at HaKV
  icases HaKV with ⟨%up, %Hup, HuOwn, HkvOwn⟩
  ihave Hrp := etcdserver.restorePre_of_apply s E x.log hwq $$ [$HkvOwn $Hkvc]
  icases Hrp with ⟨%ws, %γw, %Hγw, #Hws, Hscl, Hfrag, HwOwn, #Hfrz, HwW, ⟨HsRd, HlLive, HERD⟩, ⟨%wsk, %stck, #Hkvfk, #Hstck, Hstclk, Hwswk⟩⟩
  icombine Hkvf Hkvfk gives %Hwk
  have Hwkl : wsk = wsl := by simp at Hwk; exact GoGlobalContext.intoVal_inj_loc Hwk.symm
  subst wsk
  iunfold apply.leasesLive at HlLive
  icases HlLive with ⟨%Ll, #HlK, HlUser⟩
  iunfold lease.lessorUser at HlUser
  icases HlUser with ⟨HlOwn, HlRd, HlRv⟩
  ihave %Hwseq := isWatchableStore_agree ws wsl E.s γw γw0 $$ [$Hws $Hwsl]
  subst Hwseq
  (try wp_auto)
  -- `s.lessor.Recover(newbe, …)`: the lessor on the new backend, no lease live
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  ihave Hnwb : ownToks γB.wb ((backend.wbInit - 2) + 2) $$ [Hnwb]
  · rw [show (backend.wbInit - 2) + 2 = backend.wbInit by unfold backend.wbInit; omega]
    iexact Hnwb
  icases ownToks_add_1 2 _ γB.wb $$ Hnwb with ⟨Hnwb, Hwb2⟩
  ihave #Hlspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  wp_apply hLR lp E.γ.leases d.be d' (mvcc.lateW gx')
      (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) (1 : Qp).half
      (backend.rbData d.P D) _ Ll _ $$ [HoLe HlOwn HlRv HnOh Hwb2 HnRB]
    as ⟨HnLe, HlOwn, HlRv, HnOh, HnRB⟩
  · rw [hγ', hP']; iframe #; iframe HoLe HlOwn HlRv HnOh Hwb2 HnRB
    ipureintro; exact hlease
  (try wp_auto)
  -- `s.kv.Restore(newbe)`: the store over the image's log at the new backend
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  ihave #Hmvpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #HnB' : backend.isBackend (GF := GF) d'.γB
      d'.P
      (mvcc.lateW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P))
      d'.be $$ []
  · rw [hγ', hP', hgx']; iexact HnB
  ihave #HnSz : mvcc.keySized (GF := GF) d'.γB
      d'.P
      d'.be $$ []
  · rw [hP']; iapply HkSz $$ %d'.γB %d'.be
  have hbr' : mvcc.bridgeParams d'.P := by rw [hP']; exact hbr
  -- the restore's new backend never compacts (`Hnd`, fixed above)
  ihave #Hnd' : backend.dlNoDel d'.γB $$ []
  · rw [hγ']; iexact Hnd
  ihave #HsbT := mvcc.storeBackendT_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
    hrUR hLI hLO hSP hUL hBUR hCB hDel hID hName hSafe d' hbr' hcm'
    (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) E.γ.bucket $$ [$Hbpkg $Hschpkg $HnB' $HnSz $Hnd']
  ihave #HkcR := mvcc.keyCleanRead_of_backend hRT hrRL hrRU hrUR hID hName hSafe
    d' hbr'
    (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) E.γ.bucket $$ [$Hbpkg $Hschpkg $HnB' $HnSz $Hnd']
  ihave HnView : mvcc.kbViewC (GF := GF) (some d') E.γ.bucket 1
      (mvcc.bucketMap ([[], []] ++ R)) $$ [HnV]
  · simp only [mvcc.kbViewC, mvcc.bkViewC, hγ']
    iexists _; iframe HnV
    ipureintro; exact mvcc.keyView_of_keyImage hbr hkI
  ihave HnNC : mvcc.kbNoCmp (GF := GF) (some d') E.γ.bucket
      $$ [Hncmp]
  · simp only [mvcc.kbNoCmp, hγ']
    iapply mvcc.bkNoCmp_of_fkCl γB _ (mvcc.keyImage_noCmp hkI) $$ Hncmp
  wp_apply hRst ws E.s γw _ d' E.γ.bucket
      (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) x.log R hpre hRok
    $$ [Hscl Hfrag HwOwn HwW HnView HnNC HlateR HnRTx]
    as ⟨%p', %Hp', Hscl', Hfrag', HwOwn', #HhkP', HwW', Hold, Hnew⟩
  · iframe #; iframe Hscl Hfrag HwOwn HwW HnView HnNC
    isplitr
    · ipureintro; exact ⟨d, by rw [Hγw]; exact hkb, hcm⟩
    isplitr
    · ipureintro; exact hcm'
    isplitr
    · rw [Hγw]; iexact Hcok
    isplitr
    · iintro %p %Hp
      iapply HsbT $$ %E.s %(γw.st.withPhys p) %Hp
    isplitr
    · iintro %p %Hp
      iapply HkcR $$ %(γw.st.withPhys p) %Hp
    isplitl [HlateR]
    · simp only [mvcc.kbRegRight, mvcc.lateReg, hgx']; iexact HlateR
    rw [kbRT_some, hγ', hP']; iexact HnRTx
  (try wp_auto)
  -- the post-lock hook of the new names, installed on the new backend
  ihave #HCI' : isServerCI (GF := GF) s (γ.withPh π') ci $$ []
  · iunfold isServerCI; iframe Hcif Hisci
    rw [show consInv (GF := GF) (γ.withPh π') = consInv γ from rfl]
    iexact Hinv
  wp_apply hGTP s (γ.withPh π') ci (metaTM γB d.P) $$ [$HCI'] as %g ⟨%Hgnn, #HhkS⟩
  icases toks_take γB.wb _ 1 (by unfold backend.wbInit; omega) $$ Hnwb with ⟨Hnwb, Hwb1⟩
  wp_apply hSTP γB d.P (mvcc.lateW gx') (batchLockInv (γ.withPh π') (metaTM γB d.P)) d'.be
      (1 : Qp).half func.nil g $$ [HnOh HnH Hwb1] as ⟨HnOh, HnH⟩
  · rw [hγ']; iframe #; iframe HnOh HnH
    iunfold backend.wbTok; iexact Hwb1
  (try wp_auto)
  -- `s.consistIndex.ConsistentIndex()` (logged): read through the new backend's meta reads
  ihave #HmB' := HmetaB $$ %π' %d'.be %rfl
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
  icases toks_take γB.wb _ 2 (by unfold backend.wbInit; omega) $$ Hnwb with ⟨Hnwb, Hwb2'⟩
  ihave #HnRO : srvBeRO (GF := GF) d' $$ []
  · iunfold srvBeRO; iexists _; rw [hγ', hP', hgx']; iexact HnB
  ihave HnMon : mvcc.bkRTx (GF := GF) d'.γB d'.P d'.be $$ [Hnew]
  · rw [show mvcc.storeRT (GF := GF) (γw.st.withPhys p') = mvcc.kbRT (some d') by
      simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, Hp'.2]]
    rw [kbRT_some]
    iexact Hnew
  imod srv_be_swap s E γp d' (backend.wbInit - 2 - 1 - 2) (by omega) $$ HWP Hbm Hbo HnRO
      [Hnwb] HnMon Hlc2 with ⟨%dold, %Hdold, Hbefull, -, HoMon, #HoRO, Hbeback⟩
  · rw [hγ']; iexact Hnwb
  (try wp_auto)
  icases Hbeback $$ Hbefull with ⟨Hbm, HbeA, HγbeA⟩
  wp_apply sync.RWMutex.wp_Unlock $$ [$Hbl Hbm] as Hbr
  · iframe #; inext; iexact Hbm
  (try wp_auto)
  -- `s.r.storage.Release(snapshot)`: the snapshot's index taken, the older files released
  imod (mono_nat_own_update (uint.nat sv.Metadata'.Index') (by word)) $$ Hγt with ⟨Hγt, #Htk⟩
  wp_apply hRel stp ss sn smp DFrac.discard DFrac.discard sv.Metadata' γd img (snapTakenLb γt) hstp
    $$ [] as %rerr ⟨-, -, %Hrerr⟩
  · iframe #
    iintro !> %j %hj
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
  icases toks_take γB.wb 2 1 (by omega) $$ Hwb2' with ⟨Hwb2', Hwba⟩
  wp_apply hAR al d.be abl sfv.lg d'.be γB d.P (mvcc.lateW gx')
      (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) (1 : Qp).half
      ((backend.rbData d.P D).insert go!"lease" ∅) $$ [HoAl HnOh Hwba HnRB]
    as %aerr ⟨%Haerr, HnAl, HnOh, HnRB⟩
  · rw [hγ']; iframe #; iframe HoAl HnOh HnRB
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
  icases mvcc.writerOwn_rt (γw.st.withPhys p') $$ HwOwn' with ⟨HwRT, HwOwnK⟩
  ihave HwRT : mvcc.bkRTx (GF := GF) d'.γB d'.P d'.be $$ [HwRT]
  · rw [show mvcc.storeRT (GF := GF) (γw.st.withPhys p') = mvcc.kbRT (some d') by
      simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, Hp'.2]]
    rw [kbRT_some]; iexact HwRT
  iunfold authRecoverOk at HauR
  ihave #HauR' := HauR $$ %d.be %aubl %sfv.lg %d' %(mvcc.lateW gx')
    %(batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) %((1 : Qp).half)
    %(((backend.rbData d.P D).insert go!"lease" ∅).insert go!"alarm" ∅)
  wp_apply HauR' $$ [HoAu HnOh HwRT HnRB] as ⟨HnAu, HnOh, HwRT, HnRB⟩
  · rw [hγ', hP', hgx']; iframe #; iframe HoAu HnOh HwRT HnRB
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro
    refine ⟨?_, ?_, ?_⟩ <;>
      rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide)]
    · exact hauthb.1
    · exact hauthb.2.1
    · exact hauthb.2.2
  (try wp_auto)
  -- `s.cluster.SetBackend(schema.NewMembershipBackend(lg, newbe))`
  wp_apply hInfo $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hNMB as %mbl ⟨#Hmblg, #Hmblb⟩
  icases toks_take γB.wb 1 1 (by omega) $$ Hwb2' with ⟨-, Hwbm⟩
  ihave #Hmempkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  wp_apply hCSB cl d.be mbl sfv.lg d' (mvcc.lateW gx') (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P))
      (1 : Qp).half ((((backend.rbData d.P D).insert go!"lease" ∅).insert go!"alarm" ∅))
    $$ [HoCl HnOh Hwbm HnRB] as ⟨HnCl, HnOh, HnRB⟩
  · rw [hγ', hP', hgx']; iframe #; iframe HoCl HnOh HnRB
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
  have hdd : dold = d := by rw [hkb] at Hdold; exact (Option.some.inj Hdold).symm
  subst dold
  ihave Hold : [∗list] _x ∈ List.replicate (mvcc.nReaders - 1) (), mvcc.bkRTx (GF := GF) d.γB d.P d.be
      $$ [Hold]
  · rw [show mvcc.storeRT (GF := GF) γw.st = mvcc.kbRT (some d) by
      simp only [mvcc.storeRT, Hγw, hkb]]
    rw [kbRT_some]; iexact Hold
  ihave Hshares := bkRTx_shares d.γB d.P d.be _ $$ Hold
  ihave Hmsh := bkRTx_shares d.γB d.P d.be 1 $$ [HoMon]
  · simp only [List.replicate]; iapply BigSepL.bigSepL_cons.2; iframe HoMon
    iapply BigSepL.bigSepL_nil.2; itrivial
  ihave HoO1 : backend.bOpen (GF := GF) d.γB 1 $$ [HoOh Hshares Hmsh]
  · iapply (backend.bOpen_one_shares d.γB).2
    iframe HoOh
    have h2 := sync.actualMaxReaders_ge_2
    rw [show Int.toNat sync.rwmutex.actualMaxReaders = (mvcc.nReaders - 1) + 1 by
      unfold mvcc.nReaders; omega]
    iapply (mvcc.rep_split _ (mvcc.nReaders - 1) 1).2
    iframe
  iunfold srvBeRO at HoRO
  icases HoRO with ⟨%Pko, #HoB⟩
  wp_apply wp_fork $$ [oldbe HoO1]
  · wp_apply wp_with_defer as %defer2 defer2
    (try wp_auto)
    wp_apply hInfo $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply hClose d.γB d.P (mvcc.lateW d.gx) Pko d.be $$ [HoO1] as %cerr %Hcerr
    · iframe #; iframe HoO1
    have hcerr : cerr = GoInterface.nil := by
      rcases Hcerr with h | h
      · exact h
      · exact absurd hsop.2.2.2 h
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
      ((((backend.rbData d.P D).insert go!"lease" ∅).insert go!"alarm" ∅)) memI := by
    unfold membership.clusterImageOk at himg ⊢
    rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
      GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
      GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide)]
    exact himg
  wp_apply hCRec cl d' (mvcc.lateW gx') (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P))
      ((((backend.rbData d.P D).insert go!"lease" ∅).insert go!"alarm" ∅)) _ memI himg'
    $$ [HnCl HwRT HnRB HoMem] as ⟨HnCl, HwRT, HnRB, HnMem⟩
  · rw [hγ', hP', hgx']; iframe #; iframe HnCl HwRT HnRB HoMem
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
  -- (D22 J-T) the peers' no-remote facts go back to the transport; four of each peer's `R`s come
  -- back (dropped here: the `AddPeer`s below take the premise's eight each)
  icases Htlive with ⟨Htlive, Hpnr⟩
  iunfold trPeersNoRem at Hpnr
  icases Hpnr with ⟨%Q, %HQ, Htks⟩
  wp_apply hRAP γn t c rs Q HQ.1 HQ.2 $$ [Htlive Htks] as ⟨Htlive, -⟩
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
      "s" ∷ s_ptr ↦ s ∗
      "Htlive" ∷ trLive γn t c L ∗
      "HR8s" ∷ ([∗list] _x ∈ List.replicate (8 * ps.length - 8 * L.length) (), c.R) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z msl.len ∧ L.length ≤ (sint.Z n).toNat⌝ ∗
      "%Hcov" ∷ ⌜∀ (k : Nat) (p : Loc × w64), k < (sint.Z n).toNat → mps[k]? = some p →
        p.2 ≠ idm → p.2 ∈ L⌝) $$ [i m s Htlive HR8s]
  · iexists W64 0, _, []
    iframe i m s Htlive
    isplitl [HR8s]
    · rw [show 8 * ps.length - 8 * ([] : List w64).length = 8 * ps.length by simp]
      iexact HR8s
    ipureintro
    refine ⟨⟨by decide, by have := Hmsll.2; word, by simp⟩, fun k p hk _ _ => ?_⟩
    exact absurd hk (by simp)
  iapply wp_fupd
  wp_join (iprop(∃ (L : List w64), "s" ∷ s_ptr ↦ s ∗
      "Hmsl" ∷ msl ↦* List.map Prod.fst mps ∗
      "Hmso" ∷ ([∗list] p ∈ mps, memberDirIs (GF := GF) dir p.fst p.snd) ∗
      "Htlive" ∷ trLive γn t c L ∗
      "%Hcov" ∷ ⌜∀ f, (netRh γn).member f → f ≠ idm → f ∈ L⌝))
    at (App (App (App (Val doFor) _) _) _) with [Hmsl Hmso IH2]
    as ⟨%L, s, Hmsl, Hmso, Htlive, %Hcov⟩
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
        ipureintro
        refine ⟨⟨by word, by word, by omega⟩, ?_⟩
        rw [Hn1]
        exact membersCov_step mps _ L L _ px Hpx Hcov (fun _ h => h) (fun h => absurd rfl h)
      · have Hpid : px.2 ≠ idm := by simpa using Hif
        obtain ⟨Hne, Hpl, Hown, Hpm⟩ :=
          addPeer_dir γn dir hdir hdok ps hps px.2 Hpxps mpus Hmok.2
        have H8 : 8 ≤ 8 * ps.length - 8 * L.length := by
          have h1 : mps.length = (sint.Z msl.len).toNat := Hmsll.1
          have h2 := Hn.2.2
          have h3 : mps.length = ps.length := by rw [← Hmps, List.length_map]
          have h4 : L.length < ps.length := by omega
          omega
        icases replicate_takeN _ 8 _ H8 $$ HR8s with ⟨HR8, HR8s⟩
        wp_apply (hAP γn t c L px.2 mpu (DFrac.own 1) mpus Hne Hpl Hown
            (by rw [hlid]; exact fun h => Hpid h.symm) Hpm) $$ [Htlive Hmpus HR8]
          as ⟨Htlive, Hmpus, -⟩
        · iframe Htlive Hmpus HR8
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
        isplitl [HR8s]
        · rw [show 8 * ps.length - 8 * (L ++ [px.2]).length = 8 * ps.length - 8 * L.length - 8 by
            simp only [List.length_append, List.length_singleton]; omega]
          iexact HR8s
        ipureintro
        refine ⟨⟨by word, by word, by simp only [List.length_append, List.length_singleton]; omega⟩, ?_⟩
        rw [Hn1]
        exact membersCov_step mps idm L (L ++ [px.2]) _ px Hpx Hcov
          (fun x hx => List.mem_append_left _ hx) (fun _ => List.mem_append_right _ (by simp))
    · wp_join_done
      iexists L
      iframe
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
  wp_apply hNUA s sfv.lg al cl _ _ _ _ _ fg quota wad E.RD (DFrac.own (1 : Qp).half) Tal zal hbuq
    $$ [HbeA HERD HTal] as %ua' ⟨HbeA, HTal, %up', %opts', %Hua', %Hopts', Hube⟩
  · iframe #; iframe HbeA HERD HTal
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
  iunfold snapWalkPost
  iexists γB, d', gx', π0, p', γw, ws, g, up', opts', L, spc, Ll, jf, γcf, w0, RD0, up, sfv.lg, ws, stck
  isplitr
  · ipureintro
    exact ⟨hγ', hP', hgx', hcm', rfl, Hp'.1, Hp'.2, Hγw, hbr', Hcov, Hgnn, Hopts'⟩
  iunfold srvBemuReaderAt
  iframe
  iframe #

end proof
end EtcdGrove
end Perennial
