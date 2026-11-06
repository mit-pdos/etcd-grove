/-
**`applySnapshot`'s walk's result** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`; its named premises `authRecoverOk`, `srvMembersDir`, `lessorLookupOk`
are in `SnapRO.lean` since D22 J1a): `snapWalkPost`, what `applySnapshot`'s code leaves
(`applySnapshot_walk`, `SnapApplyWalk.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__NewUberApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreLaws

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

theorem toks_take (γ : GName) (n k : Nat) (h : k ≤ n) :
    ownToks (GF := GF) γ n ⊢ ownToks γ (n - k) ∗ ownToks γ k := by
  have := (ownToks_add (GF := GF) k (n - k) γ).1
  rwa [Nat.sub_add_cancel h] at this

/-- Two copies of `R` (the backend's two counted slots the open law gives back). -/
theorem rep_two (R : IProp GF) : ([∗list] _x ∈ List.replicate 2 (), R) ⊣⊢ R ∗ R := by
  simp only [List.replicate]
  refine BigSepL.bigSepL_cons.trans ?_
  refine sep_congr .rfl ?_
  refine BigSepL.bigSepL_cons.trans ?_
  refine (sep_congr .rfl BigSepL.bigSepL_nil).trans ?_
  exact sep_emp

/-- The counted stock's open shares: the store's `rdStockN - 2` and two more. -/
theorem rdStock_split2 (R : IProp GF) :
    ([∗list] _x ∈ List.replicate backend.rdStockN (), R) ⊣⊢
      ([∗list] _x ∈ List.replicate (backend.rdStockN - 2) (), R) ∗ R ∗ R := by
  have h : backend.rdStockN = (backend.rdStockN - 2) + 2 := by rw [backend.rdStockN_val]
  conv => lhs; rw [h]
  refine (backend.bigSepL_replicate_add R _ 2).trans ?_
  exact sep_congr .rfl (rep_two R)

-- (D22 J1a, 2026-10-26) `srvAuthRecoverOk` (now `authRecoverOk`), `srvMembersDir` and
-- `lessorLookupOk` moved to `SnapRO.lean`.

/-- **What `applySnapshot`'s code leaves** (S8d's walk, `applySnapshot_walk`): the server's
resources at the snapshot's backend `d'` (opened at the snapshot's index `sv.Metadata'.Index'`),
from which `applySnapshot.spec`'s postcondition is assembled. (Strict M1, 2026-11-06: over mvcc's
API, the store restored in place by `KV.Restore.contract`: its open token, its backend's whole
share at `d'` under the new names' batch lock, the apply thread's halves at the image's committed
log `A'`, the lessor's live set empty; the new backend's two reader tokens the open law gives back,
the apply thread's (`apply.bkRT d'`) and the storage-version monitor's, the latter in the write
budget's invariant since the swap. Until then the store's internals: `storeCloserM`, `writerFrag`,
`watchWriter`, `writerOwn`, the watchable store, `kbWTSupplyM`.) -/
def snapWalkPost (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data) (A A' : List EntryModel)
    (x : apply.ApplyKV) (ss : Loc) (bp : GoString) (hk : Loc) (γt : GName) (γn : NetNames GF)
    (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc)
    (memI : GMap w64 apply.MemberM) (quota : w64) (wad : time.Duration) : IProp GF :=
  iprop(∃ (d' : mvcc.KBReal) (π0 : ApplyPhys) (g : GoFunc) (up' : Loc)
      (opts' : apply.ApplierOptions) (L : List w64) (spc : Loc) (jf : Nat)
      (γcf : GName) (w0 : GoInterface) (RD0 : IProp GF) (up : Loc) (lg : Loc),
    ⌜d'.P = d.P ∧ d'.cm = true ∧ π0.m0 = (sv.Metadata'.Index', π0.m0.2) ∧ mvcc.bridgeParams d'.P ∧
      (∀ f, (netRh γn).member f → f ≠ idm → f ∈ L) ∧ g ≠ func.nil ∧
      opts'.Logger' = lg ∧ opts'.KV' = E.kv ∧
      opts'.AlarmStore' = al ∧ opts'.AuthStore' = auth.authIface ast ∧
      opts'.Lessor' = lease.lessorIface lp ∧ opts'.Cluster' = cl ∧
      opts'.ConsistentIndex' = ciIface ci ∧ opts'.Backend' = srvBeIface d'.be ∧
      opts'.QuotaBackendBytesCfg' = quota ∧ opts'.WarningApplyDuration' = wad ∧
      opts'.RaftStatus' = interface.mkOk EtcdServer.ty.PointerType #s ∧
      opts'.SnapshotServer' = interface.mkOk EtcdServer.ty.PointerType #s⌝ ∗
    -- the snapshot's backend and what reads and writes it (persistent)
    backend.isBackend d'.γB d'.P (mvcc.api.mvccW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) d'.be ∗
    -- (2026-11-02, branch `snap-window`) its hooks the server's `s.beHooks` (`OpenSnapshotBackend`'s)
    backend.hooksAt d'.be (storage.hooksIface hk) ∗ structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
    backend.isStopChans d'.γB d'.be ∗ mvcc.keySized d'.γB d'.P d'.be ∗
    isMetaBackend (interface.mkOk go_etcd_io.etcd.server.v3.storage.backend.backend.ty.PointerType #d'.be)
      (⊤ \ ↑applyN) (readView (γ.withPh (futPhys π0 d'.γB))) ∗
    isServerCI s (γ.withPh (futPhys π0 d'.γB)) ci ∗
    hookSpec (γ.withPh (futPhys π0 d'.γB)) ci (metaTM d'.γB d.P) #g ∗
    monoListIdxOwn γ.fut jf (futPhys π0 d'.γB, γcf) ∗ applyRegd (γ.withPh (futPhys π0 d'.γB)) ∗
    srvBeRO d' ∗
    srvWAddr s ↦□ w0 ∗ srvLgAddr s ↦□ lg ∗
    waitOk w0 RD0 (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ∗
    -- the apply thread's own (spatial)
    backend.plHook d'.γB g ∗
    applyThread (γ.withPh (futPhys π0 d'.γB)) (stLoaded (γ.withPh (futPhys π0 d'.γB))
      { k := W64 0, p := sv.Metadata'.Index', eff := sv.Metadata'.Index', pending := false }) ∗
    applyBackend (γ.withPh (futPhys π0 d'.γB)) ci
      (interface.mkOk go_etcd_io.etcd.server.v3.storage.backend.backend.ty.PointerType #d'.be) ∗
    dghostVar E.γbe (DFrac.own (1 : Qp).half.half) (bkKey d') ∗ srvBemuReaderAt s E.γbe ∗
    srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
    monoNatAuthOwn γt 1 (uint.nat sv.Metadata'.Index') ∗
    authBeOn ast d'.be ∗ clusterBeOn cl d'.be ∗ lease.lessorBeOn lp d'.be ∗
    lease.leaseOwn (mvcc.api.mvccLeases E.γ) [] ∅ ∗ lease.lessorRdOf (mvcc.api.mvccLeases E.γ) ∗
    lease.leaseRevokers (mvcc.api.mvccLeases E.γ) [] ∗
    apply.bkRT d' ∗
    -- (2026-11-02, the backend-auth-split stage) the cluster's buckets idle, the others a part
    backend.rbOwnIn d'.γB membership.clusterBkts
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D))) ∗
    backend.rbPart d'.γB (fun n => ¬ membership.clusterBkts n)
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D))) ∗
    membership.clusterMem cl memI ∗ backend.bOpen d'.γB (1 : Qp).half ∗
    -- (2026-11-02, the backend-auth-split stage) the new backend's pool of readers
    backend.bkRPool d'.γB d'.P d'.be ∗
    -- (strict M1) the store, restored: its open token, its backend's whole share, the apply thread's
    -- halves at the image's committed log
    mvcc.api.mvccOpen E.γ ∗
    mvcc.api.mvccBackend E.γ 1 d' (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) ∗
    srvApi.wSt E.γs (kvModel γr.kv A') (crevOf γr.kv A') ∗ srvApi.crOwn E.γs (crevOf γr.kv A') ∗
    trLive γn t c L ∗ srvLgReader s ∗
    epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
    epDiskSnapAddr ep ↦ sv.Metadata'.Index' ∗ epMemSnapAddr ep ↦ sv.Metadata'.Index' ∗
    epConfStateAddr ep ↦ spc ∗ csOptA spc DFrac.discard sv.Metadata'.ConfState' ∗
    backend.pathOwn bp ∗ alarmBeOn al d'.be ∗
    -- (2026-11-01, J8a) the old KV's reader resource of the auth store (`NewUberApplier` takes none)
    E.RD ∗
    (∀ E1 : apply.AEnv GF, apply.backendOptsOk E1 opts' -∗
      apply.uberIs E1 up' opts' ∗ apply.uberOwn E1 up' (apply.alarmChain E1.authOn false false)) ∗
    srvUberApplyAddr s ↦ (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) ∗
    -- what is left of the old backend's and the old applier's
    backend.rbOwn d.γB (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk ∗
    revAuth E x.log ∗ srvAuthApplyRes s E ∗ RD0 ∗ apply.uberOwn E up x.chain)

end proof
end EtcdGrove
end Perennial
