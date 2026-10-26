/-
**`applySnapshot`'s named premises and its walk's result** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`): the premises S8d takes from the auth track (`srvAuthRecoverOk`) and
from boot (`srvMembersDir`), and `snapWalkPost`, what `applySnapshot`'s code leaves
(`applySnapshot_walk`, `SnapApplyWalk.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Uint64
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyOpen
public import Spec.go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__OnPreCommitUnsafe
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__UnsafeSave
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Restore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestorePre
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreMoves
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Release
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewAlarmBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__Recover
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewAuthBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewMembershipBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Recover
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__RemoveAllPeers
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__NewUberApplier

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

theorem kbP_mk (d : mvcc.KBReal) (a : backend.BNames) (b : Loc) (g : GName) :
    ({ γB := a, BT := d.BT, hookMax := d.hookMax, limit := d.limit, be := b, gx := g } :
      mvcc.KBReal).P = d.P := rfl
theorem kbgx_mk (d : mvcc.KBReal) (a : backend.BNames) (b : Loc) (g : GName) :
    ({ γB := a, BT := d.BT, hookMax := d.hookMax, limit := d.limit, be := b, gx := g } :
      mvcc.KBReal).gx = g := rfl

theorem toks_take (γ : GName) (n k : Nat) (h : k ≤ n) :
    ownToks (GF := GF) γ n ⊢ ownToks γ (n - k) ∗ ownToks γ k := by
  have := (ownToks_add (GF := GF) k (n - k) γ).1
  rwa [Nat.sub_add_cancel h] at this

theorem kbRT_some (d : mvcc.KBReal) : mvcc.kbRT (GF := GF) (some d) = mvcc.bkRTx d.γB d.P d.be := rfl

/-- The auth store's `Recover` on a new backend (S8d's named premise, the auth track's). -/
def srvAuthRecoverOk (ast : Loc) : IProp GF :=
  iprop(□ (∀ (oldbe abl lg : Loc) (dn : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
          (r : GMap GoString backend.BktData),
        {{ authBeOn ast oldbe ∗ ⌜lg ≠ null⌝ ∗
            structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
              (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
                #dn.be : GoInterface) ∗
            structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg ∗
            backend.isBackend dn.γB dn.P W Pk dn.be ∗ backend.bOpen dn.γB qo ∗
            mvcc.bkRTx dn.γB dn.P dn.be ∗ backend.rbOwn dn.γB r ∗
            ⌜(r.lookup go!"auth").getD ∅ = authBoot ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
              (r.lookup go!"authRoles").getD ∅ = ∅⌝ }}
          (App (Val (ast @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
            go!"Recover")) (Val #(authBkIface abl)))
        {{ RET #(); authBeOn ast dn.be ∗ backend.bOpen dn.γB qo ∗ mvcc.bkRTx dn.γB dn.P dn.be ∗
            backend.rbOwn dn.γB r }}))

instance srvAuthRecoverOk_persistent (ast : Loc) : Persistent (srvAuthRecoverOk (GF := GF) ast) := by
  unfold srvAuthRecoverOk; infer_instance

/-- `bootOk`'s contract of the cluster's `Members()` (S8d's named premise, threaded from `NewServer`). -/
def srvMembersDir (cl : Loc) (ps : List w64) (dir : w64 → List GoString) : IProp GF :=
  iprop(□ (∀ Φ : val → IProp GF,
    (∀ (sl : GoSlice) (ms : List (Loc × w64)), ⌜ms.map Prod.snd = ps⌝ -∗
      sl ↦* ms.map Prod.fst -∗ ([∗list] p ∈ ms, memberDirIs dir p.1 p.2) -∗ Φ #sl) -∗
    WP (App (Val (cl @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Members"))
      (Val #())) {{ Φ }}))

instance srvMembersDir_persistent (cl : Loc) (ps : List w64) (dir : w64 → List GoString) :
    Persistent (srvMembersDir (GF := GF) cl ps dir) := by
  unfold srvMembersDir; infer_instance

/-- **What `applySnapshot`'s code leaves** (S8d's walk, `applySnapshot_walk`): the server's
resources at the snapshot's backend (`d'`, opened at the snapshot's index `sv.Metadata'.Index'`),
from which `applySnapshot.spec`'s postcondition is assembled. -/
def snapWalkPost (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data) (A : List EntryModel)
    (x : apply.ApplyKV) (R : mvcc.Log) (ss hk : Loc) (γt : GName) (γn : NetNames GF) (t : Loc)
    (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc) (memI : GMap w64 apply.MemberM)
    (quota : w64) (wad : time.Duration) (Tal : IProp GF) (zal : Bool) : IProp GF :=
  iprop(∃ (γB : backend.BNames) (d' : mvcc.KBReal) (gx : GName) (π0 : ApplyPhys)
      (p' : mvcc.PhysNames) (γw : mvcc.WsNames) (ws : Loc) (g : GoFunc) (up' : Loc)
      (opts' : apply.ApplierOptions) (L : List w64) (spc : Loc) (Ll : List w64) (jf : Nat)
      (γcf : GName) (w0 : GoInterface) (RD0 : IProp GF) (up : Loc) (lg : Loc),
    ⌜d'.γB = γB ∧ d'.P = d.P ∧ d'.gx = gx ∧ π0.m0 = (sv.Metadata'.Index', sv.Metadata'.Term') ∧
      p'.bucket = E.γ.bucket ∧ p'.kb = some d' ∧ γw.st = E.γ ∧ mvcc.bridgeParams d'.P ∧
      (∀ f, (netRh γn).member f → f ≠ idm → f ∈ L) ∧
      opts'.Logger' = lg ∧
      opts'.KV' = interface.mkOk go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty.PointerType #ws ∧
      opts'.AlarmStore' = al ∧ opts'.AuthStore' = auth.authIface ast ∧
      opts'.Lessor' = lease.lessorIface lp ∧ opts'.Cluster' = cl ∧
      opts'.ConsistentIndex' = ciIface ci ∧ opts'.Backend' = srvBeIface d'.be ∧
      opts'.QuotaBackendBytesCfg' = quota ∧ opts'.WarningApplyDuration' = wad ∧
      opts'.RaftStatus' = interface.mkOk EtcdServer.ty.PointerType #s ∧
      opts'.SnapshotServer' = interface.mkOk EtcdServer.ty.PointerType #s⌝ ∗
    -- the snapshot's backend and what reads and writes it (persistent)
    backend.isBackend d'.γB d'.P (mvcc.lateW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) d'.be ∗
    backend.isStopChans γB d'.be ∗ mvcc.keySized d'.γB d'.P d'.be ∗
    backend.hooksOk d.P (fun _ => mvcc.lateW gx)
      (fun γB => batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) (storage.hooksIface hk) ∗
    (∀ s γ1, ⌜γ1.bucket = E.γ.bucket ∧ γ1.kb = some d'⌝ →
      mvcc.storeBackendT (interface.mkOk go_etcd_io.etcd.server.v3.storage.backend.backend.ty.PointerType #d'.be) s γ1
        (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P))) ∗
    (∀ γ1, ⌜γ1.bucket = E.γ.bucket ∧ γ1.kb = some d'⌝ →
      mvcc.keyCleanRead (interface.mkOk go_etcd_io.etcd.server.v3.storage.backend.backend.ty.PointerType #d'.be)
        (mvcc.bucketViewC γ1) (mvcc.storeRT γ1)) ∗
    isMetaBackend (interface.mkOk go_etcd_io.etcd.server.v3.storage.backend.backend.ty.PointerType #d'.be)
      (⊤ \ ↑applyN) (readView (γ.withPh (futPhys π0 γB))) ∗
    isServerCI s (γ.withPh (futPhys π0 γB)) ci ∗
    hookSpec (γ.withPh (futPhys π0 γB)) ci (metaTM γB d.P) #g ∗
    monoListIdxOwn γ.fut jf (futPhys π0 γB, γcf) ∗ applyRegd (γ.withPh (futPhys π0 γB)) ∗
    srvBeRO d' ∗ mvcc.isWatchableStore ws E.s γw ∗ mvcc.crevFrozen γw.st ∗
    txn.leasesKnown Ll (mvcc.stateAfter x.log) ∗
    mvcc.hookP (γw.st.withPhys p') (batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) ∗
    srvKVAddr s ↦□ (interface.mkOk go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty.PointerType #ws : GoInterface) ∗
    srvWAddr s ↦□ w0 ∗ srvLgAddr s ↦□ lg ∗
    waitOk w0 RD0 (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ∗
    -- the apply thread's own (spatial)
    backend.plHook γB g ∗
    applyThread (γ.withPh (futPhys π0 γB)) (stLoaded (γ.withPh (futPhys π0 γB))
      { k := W64 0, p := sv.Metadata'.Index', eff := sv.Metadata'.Index', pending := false }) ∗
    applyBackend (γ.withPh (futPhys π0 γB)) ci
      (interface.mkOk go_etcd_io.etcd.server.v3.storage.backend.backend.ty.PointerType #d'.be) ∗
    dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d' ∗ srvBemuReaderAt s E.γbe ∗
    srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
    monoNatAuthOwn γt 1 (uint.nat sv.Metadata'.Index') ∗
    alarmBeOn al d'.be ∗ authBeOn ast d'.be ∗ clusterBeOn cl d'.be ∗ lease.lessorBeOn lp d'.be ∗
    lease.leaseOwn E.γ.leases [] ∗ lease.lessorRdOf E.γ.leases ∗
    mvcc.bkRTx d'.γB d'.P d'.be ∗
    backend.rbOwn d'.γB (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D))) ∗
    membership.clusterMem cl memI ∗ backend.bOpen d'.γB (1 : Qp).half ∗
    mvcc.storeCloser E.s (γw.st.withPhys p') ∗ mvcc.writerFrag (γw.st.withPhys p') ∗
    mvcc.watchWriter γw ([[], []] ++ R) ∗
    (mvcc.storeRT (γw.st.withPhys p') -∗ mvcc.writerOwn (γw.st.withPhys p')) ∗
    mvcc.storeReader E.s E.γ ∗ trLive γn t c (rs.1, L) ∗ srvLgReader s ∗
    epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
    epDiskSnapAddr ep ↦ sv.Metadata'.Index' ∗ epMemSnapAddr ep ↦ sv.Metadata'.Index' ∗
    epConfStateAddr ep ↦ spc ∗ csOptA spc DFrac.discard sv.Metadata'.ConfState' ∗
    backend.pathOwn (snap.snapDBPath ss sv.Metadata'.Index') ∗ Tal ∗
    (∀ E1 : apply.AEnv GF, ⌜E1.RD = E.RD⌝ -∗ apply.backendOptsOk E1 opts' -∗
      apply.uberIs E1 up' opts' ∗ ∃ ns cr, ⌜zal = true → ns = false ∧ cr = false⌝ ∗
        apply.uberOwn E1 up' (apply.alarmChain E1.authOn ns cr)) ∗
    srvUberApplyAddr s ↦ (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) ∗
    -- what is left of the old backend's and the old applier's
    backend.rbOwn d.γB (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A)).bk ∗
    revAuth E x.log ∗ RD0 ∗ apply.uberOwn E up x.chain)

end proof
end EtcdGrove
end Perennial
