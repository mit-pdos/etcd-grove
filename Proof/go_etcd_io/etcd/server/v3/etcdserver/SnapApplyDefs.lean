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
-- (the auth-on pair, P6.2) the auth row by the mode (`snapAuthRowM`); `isServerM`, `srvApplyKVM`
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyAuthM

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

theorem kbP_mk (d : mvcc.KBReal) (a : backend.BNames) (b : Loc) (g : GName) :
    ({ d with γB := a, be := b, gx := g, cm := false } : mvcc.KBReal).P = d.P := rfl
theorem kbgx_mk (d : mvcc.KBReal) (a : backend.BNames) (b : Loc) (g : GName) :
    ({ d with γB := a, be := b, gx := g, cm := false } : mvcc.KBReal).gx = g := rfl

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

/-- **The apply thread's two halves of the live set agree, and move together** (the lease-expiry
plan's S2–S4, Probe 4): in a cluster that grants leases they agree; both go to `L'`. -/
theorem ltHalf_agree_upd (E : apply.AEnv GF) (L T L' : List w64) :
    ⊢ apply.ltHalf E L -∗ apply.ltHalf E T ==∗
      ⌜E.lg = true → L = T⌝ ∗ apply.ltHalf E L' ∗ apply.ltHalf E L' := by
  unfold apply.ltHalf
  cases h : E.lg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro - - !>
    isplitr
    · ipureintro; intro h'; cases h'
    isplitl <;> itrivial
  · simp only [↓reduceIte]
    iintro H1 H2
    icombine H1 H2 gives %Hv
    have Heq := Hv.2
    imod ghostVar_update_halves L' E.γlt L T $$ H1 H2 with ⟨H1, H2⟩
    imodintro
    iframe H1 H2
    ipureintro; exact fun _ => Heq

/-- **In the monotone mode every id the lessor ever had is live** (the lease-expiry plan's S2–S4,
Probe 4; `lease.ever_live_mono` at the apply thread's half of the ever set): given back. -/
theorem ever_live_modeM (E : apply.AEnv GF) (lp : Loc) (mono : Bool) (U L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (hmlg : mono = true → E.lg = true) :
    lease.lessorInv lp (mvccLeases E.γ) ∗ lease.lessorModeIs (mvccLeases E.γ) mono ∗ apply.everOwn E U ∗
      lease.leaseOwn (mvccLeases E.γ) L I ⊢
    |={⊤}=> apply.everOwn E U ∗ lease.leaseOwn (mvccLeases E.γ) L I ∗ ⌜mono = true → ∀ u ∈ U, u ∈ L⌝ := by
  cases mono
  · iintro ⟨-, -, H1, H2⟩
    imodintro
    iframe H1 H2
    ipureintro; intro h; cases h
  · have hl := hmlg rfl
    rw [apply.everOwn_true E U hl]
    iintro ⟨#Hinv, #Hm, H1, H2⟩
    ihave #Hrd := lease.lessorInv_rdInv lp (mvccLeases E.γ) $$ Hinv
    imod lease.ever_live_mono (mvccLeases E.γ) U L I ⊤ (by simp) $$ [Hrd Hm H1 H2] with ⟨H1, H2, %H⟩
    · iframe Hrd Hm H1 H2
    imodintro
    iframe H1 H2
    ipureintro; exact fun _ => H

-- (D22 J1a, 2026-10-26) `srvAuthRecoverOk` (now `authRecoverOk`), `srvMembersDir` and
-- `lessorLookupOk` moved to `SnapRO.lean`.

/-- **What `applySnapshot`'s code leaves** (S8d's walk, `applySnapshot_walk`): the server's
resources at the snapshot's backend `d'` (opened at the snapshot's index `sv.Metadata'.Index'`),
from which `applySnapshot.spec`'s postcondition is assembled. (Strict M1, 2026-11-06: over mvcc's
API, the store restored in place by `KV.Restore.contract`: its open token, its backend's whole
share at `d'` under the new names' batch lock, the apply thread's halves at the image's committed
log `A'`; the new backend's two reader tokens the open law gives back, the apply thread's
(`apply.bkRT d'`) and the storage-version monitor's, the latter in the write budget's invariant
since the swap. Until then the store's internals: `storeCloserM`, `writerFrag`, `watchWriter`,
`writerOwn`, the watchable store, `kbWTSupplyM`.) (The lease-expiry plan's S2–S4, Probe 4,
2026-11-05) The lessor at the image's records `recs` (`Recover`'s): its live set `Lr` with no item,
both halves of the apply thread's live set at `Lr`, the ids it ever had with the records' added, the
records' requests `reqOf`, the image's lease bucket kept; (P6.2, 2026-11-03) the auth row by the
mode (`snapAuthRowM`), the apply thread's share of the new backend's open token by the mode
(`srvOpenQ`); (the restart plan's R2b-3d/R2d) the stop channels at the store's write invariant and
the batch lock, the hooks' contract (`hooksOk`), the backend's file at `bp`. (The mvcc merge,
2026-11-06: `lean`'s walk post with the store's part over the API; the KV model by the mode,
`kvModelM E.authOn`.) -/
def snapWalkPost (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data) (A A' : List EntryModel)
    (x : apply.ApplyKV) (ss : Loc) (bp : GoString) (hk : Loc) (γt : GName) (γn : NetNames GF)
    (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc)
    (memI : GMap w64 apply.MemberM) (quota : w64) (wad : time.Duration) (Lr : List w64)
    (recs : List (w64 × w64 × w64)) (U : List w64) (reqOf : w64 → w64) : IProp GF :=
  iprop(∃ (d' : mvcc.KBReal) (π0 : ApplyPhys) (g : GoFunc) (up' : Loc)
      (opts' : apply.ApplierOptions) (L : List w64) (spc : Loc) (jf : Nat)
      (γcf : GName) (w0 : GoInterface) (RD0 : IProp GF) (up : Loc) (lg : Loc) (ua : GoInterface),
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
    backend.isStopChans d'.γB d'.P (mvcc.api.mvccW d'.gx)
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) d'.be ∗
    mvcc.keySized d'.γB d'.P d'.be ∗
    backend.hooksOk d.P (fun _ => mvcc.api.mvccW d'.gx)
      (fun γB => batchLockInv (γ.withPh (futPhys π0 γB)) (metaTM γB d.P)) (storage.hooksIface hk) ∗
    isMetaBackend (interface.mkOk go_etcd_io.etcd.server.v3.storage.backend.backend.ty.PointerType #d'.be)
      (⊤ \ ↑applyN) (readView (γ.withPh (futPhys π0 d'.γB))) ∗
    isServerCI s (γ.withPh (futPhys π0 d'.γB)) ci ∗
    hookSpec (γ.withPh (futPhys π0 d'.γB)) ci (metaTM d'.γB d.P) #g ∗
    monoListIdxOwn γ.fut jf (futPhys π0 d'.γB, γcf) ∗ applyRegd (γ.withPh (futPhys π0 d'.γB)) ∗
    srvBeRO d' ∗
    srvWAddr s ↦□ w0 ∗ srvLgAddr s ↦□ lg ∗
    waitOk w0 RD0 (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ∗
    -- the apply thread's own (spatial); (P6.2) the hook frozen at `g` (strict M1 had the exclusive
    -- half `plHook d'.γB g`; the mvcc merge, 2026-11-06, takes `lean`'s frozen hook)
    backend.plHookRO d'.γB g ∗
    applyThread (γ.withPh (futPhys π0 d'.γB)) (stLoaded (γ.withPh (futPhys π0 d'.γB))
      { k := W64 0, p := sv.Metadata'.Index', eff := sv.Metadata'.Index', pending := false }) ∗
    applyBackend (γ.withPh (futPhys π0 d'.γB)) ci
      (interface.mkOk go_etcd_io.etcd.server.v3.storage.backend.backend.ty.PointerType #d'.be) ∗
    dghostVar E.γbe (DFrac.own (1 : Qp).half.half) (bkKey d') ∗ srvBemuReaderAt s E.γbe ∗
    srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
    monoNatAuthOwn γt 1 (uint.nat sv.Metadata'.Index') ∗
    authBeOn ast d'.be ∗ clusterBeOn cl d'.be ∗ lease.lessorBeOn lp d'.be ∗
    lease.leaseOwn (mvccLeases E.γ) Lr ∅ ∗ lease.lessorRdOf (mvccLeases E.γ) ∗
    lease.leaseRevokers (mvccLeases E.γ) Lr ∗
    apply.ltHalf E Lr ∗ apply.ltHalf E Lr ∗ apply.everOwn E (U ++ recs.map (·.1)) ∗
    □ ([∗list] x ∈ recs, lease.leaseReqIs (mvccLeases E.γ) x.1 (reqOf x.1)) ∗
    -- (2026-11-04, the lease-expiry plan's step 2) the lessor's range deleter (`srvApplyKV`'s): its
    -- owner's half at the store's `Write` (the mvcc merge, 2026-11-06: `lean`'s `lease.rdAt
    -- E.γ.leases E.s`, the deleter at every watchable store over the inner store, restated at the
    -- API's `mvccDeleter`)
    -- MERGE-TODO(deleter-after-recover): the walk rebuilds `mvccDeleter rd E.γ` for the new closure
    -- after `lessor.Recover` (from `KV.Write.contract`: an additive law `mvccDeleter_of_write`, or
    -- inline)
    (∃ rd : GoFunc, lease.rdOwn (mvccLeases E.γ) rd ∗ mvcc.api.mvccDeleter rd E.γ) ∗
    apply.bkRT d' ∗
    -- (2026-11-02, the backend-auth-split stage) the cluster's buckets idle, the others a part (the
    -- lease-expiry plan's S2–S4: the image's lease bucket kept; P6.2: the part by the auth mode)
    backend.rbOwnIn d'.γB membership.clusterBkts
      (<[go!"alarm" := ∅]> (<[go!"lease" := ((backend.rbData d.P D).lookup go!"lease").getD ∅]> (backend.rbData d.P D))) ∗
    backend.rbPart d'.γB (restSet E.authMode)
      (<[go!"alarm" := ∅]> (<[go!"lease" := ((backend.rbData d.P D).lookup go!"lease").getD ∅]> (backend.rbData d.P D))) ∗
    -- (P6.2, 2026-11-03) the apply thread's share of the new backend's open token by the mode
    membership.clusterMem cl memI ∗ backend.bOpen d'.γB (srvOpenQ E.authMode) ∗
    -- (2026-11-02, the backend-auth-split stage) the new backend's pool of readers
    backend.bkRPool d'.γB d'.P d'.be ∗
    -- (strict M1) the store, restored: its open token, its backend's whole share, the apply thread's
    -- halves at the image's committed log (the mvcc merge: its model by the mode, `kvModelM`)
    mvcc.api.mvccOpen E.γ ∗
    mvcc.api.mvccBackend E.γ 1 d' (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) ∗
    srvApi.wSt E.γs (kvModelM E.authOn γr.kv A') (crevOf γr.kv A') ∗ srvApi.crOwn E.γs (crevOf γr.kv A') ∗
    trLive γn t c L ∗ srvLgReader s ∗
    epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
    epDiskSnapAddr ep ↦ sv.Metadata'.Index' ∗ epMemSnapAddr ep ↦ sv.Metadata'.Index' ∗
    epConfStateAddr ep ↦ spc ∗ csOptA spc DFrac.discard sv.Metadata'.ConfState' ∗
    backend.pathOwn bp ∗ backend.bFile d'.γB bp ∗ alarmBeOn al d'.be ∗
    -- (2026-11-01, J8a) the old KV's reader resource of the auth store (`NewUberApplier` takes none)
    E.RD ∗
    (∀ E1 : apply.AEnv GF, apply.backendOptsOk E1 opts' -∗
      apply.uberIs E1 up' opts' ∗ apply.uberOwn E1 up' (apply.alarmChain E1.authOn false false)) ∗
    srvUberApplyAddr s ↦ (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) ∗
    -- what is left of the old applier's: (P6.2, 2026-11-03) the auth row by the mode
    -- (`snapAuthRowM`: on, the new backend's at the image's state; until then the old one's
    -- `srvAuthApplyRes`, and the old backend's buckets, which nothing used)
    revAuth E x.log ∗
    snapAuthRowM E.authMode s E ua ast γr A' d'
      (batchLockInv (γ.withPh (futPhys π0 d'.γB)) (metaTM d'.γB d.P)) g ∗
    RD0 ∗ apply.uberOwn E up x.chain)
    -- MERGE-TODO(close): `lean`'s post also held the watchable store's own closer's parts (`wsk`'s
    -- `stopc`, `mvcc.stopCloser`, `mvcc.wsWaiter`, from `restorePre_of_apply`): over the API the
    -- store's close right is `mvccOpen E.γ` above.

/-- **`srvSnapApplied` in the server's auth mode `on`** (P6.2, 2026-11-03, F9): the server's view
and the applier row in the mode (`isServerM`, `srvApplyKVM` at the image's auth state, the state
after its log `A'`), the apply thread's share of the new backend's open token by the mode
(`srvOpenQ`); off, `srvSnapApplied` (`srvSnapAppliedG_off`). (The mvcc merge, 2026-11-06: as
`SnapRO`'s `srvSnapApplied`, over mvcc's API: the backend by the tie, the KV at the image's model by
the mode, `kvModelM on γr.kv A'`, and its compaction revision, no closer, the KV `□ isMvcc`.) -/
def srvSnapAppliedG (on : Bool) (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (A' : List EntryModel) (ss : Loc) (bp : GoString) (γt : GName)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc) :
    IProp GF :=
  iprop(∃ (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (E' : apply.AEnv GF) (b' : GoInterface)
      (st' : ApplyState) (d' : mvcc.KBReal) (x' : apply.ApplyKV) (cs' : Loc) (L : List w64),
    ⌜beSucc γ E γ' E' ∧ E'.BkTie = srvBkTie d' ∧ d'.P = d.P ∧
      E'.RO = srvRestOwnH E'.authMode d'.γB cl (srvObjsOn al ast lp cl d'.be) ∧
      loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' ∧
      x'.log = kvModelM on γr.kv A' ∧ x'.crev = crevOf γr.kv A' ∧
      x'.chain = apply.alarmChain E.authOn false false ∧
      (∀ f, (netRh γn).member f → f ≠ idm → f ∈ L)⌝ ∗
    isServerM on s γ' ci TM' E' ρ γr ∗
    epAppliedIAddr ep ↦ sv.Metadata'.Index' ∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' ∗
    epDiskSnapAddr ep ↦ sv.Metadata'.Index' ∗ epMemSnapAddr ep ↦ sv.Metadata'.Index' ∗
    epConfState ep cs' ∗ csOptA cs' DFrac.discard sv.Metadata'.ConfState' ∗
    applyThread γ' st' ∗ applyBackend γ' ci b' ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
    srvApplyKVM on s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') ∗ srvRest E' γr A' ∗
    -- MERGE-TODO(close): `lean`'s `srvKVCloserW s E'` was here (`SnapRO`, "MERGE-TODO(close)")
    srvStopChans γ' d' ∗ backend.bOpen d'.γB (srvOpenQ E'.authMode) ∗
    monoNatAuthOwn γt 1 (uint.nat sv.Metadata'.Index') ∗
    backend.pathOwn bp ∗ backend.bFile d'.γB bp ∗
    trLive γn t c L ∗
    (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E'.γ ∗ ⌜kv = E'.kv⌝))

/-- **`srvSnapAppliedG`'s `off` case is `srvSnapApplied`.** -/
theorem srvSnapAppliedG_off (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (A' : List EntryModel) (ss : Loc) (bp : GoString) (γt : GName)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc)
    (hoff : E.authMode = .off) :
    srvSnapAppliedG (GF := GF) false s ep sv γ ci E ρ γr d A' ss bp γt γn t c rs idm lp al ast cl ⊢
      srvSnapApplied s ep sv γ ci E ρ γr d A' ss bp γt γn t c rs idm lp al ast cl := by
  unfold srvSnapAppliedG srvSnapApplied
  iintro ⟨%γ', %TM', %E', %b', %st', %d', %x', %cs', %L, %Hp, H⟩
  obtain ⟨-, p, P, f, c', RO, RW, rfl⟩ := Hp.1
  have e : srvOpenQ (E.onBe p P f c' RO RW).authMode = (1 : Qp).half := by
    show srvOpenQ E.authMode = _; rw [hoff]; rfl
  rw [e, isServerM_false, srvApplyKVM_false]
  iexists γ', TM', _, b', st', d', x', cs', L
  isplitr
  · ipureintro; exact Hp
  iexact H

/-- **`srvSnapApplied` with auth on** (the auth-on snapshot plan's Freeze; P6.2, 2026-11-03:
`srvSnapAppliedG true`, the Draft's body): the server's row in the mode, the applier at the image's
auth state (the state after `A'`). -/
abbrev srvSnapAppliedOn (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (A' : List EntryModel) (ss : Loc) (bp : GoString) (γt : GName)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc) :
    IProp GF :=
  srvSnapAppliedG true s ep sv γ ci E ρ γr d A' ss bp γt γn t c rs idm lp al ast cl

/-- **`specSnapM`'s post, by the mode** (F9): lean's `srvSnapApplied` off, `srvSnapAppliedOn`
on. -/
def srvSnapAppliedM (on : Bool) (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (A' : List EntryModel) (ss : Loc) (bp : GoString) (γt : GName)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc) :
    IProp GF :=
  match on with
  | false => srvSnapApplied s ep sv γ ci E ρ γr d A' ss bp γt γn t c rs idm lp al ast cl
  | true => srvSnapAppliedOn s ep sv γ ci E ρ γr d A' ss bp γt γn t c rs idm lp al ast cl

/-- **`srvSnapAppliedG` is `srvSnapAppliedM` in a mode the server runs in.** -/
theorem srvSnapAppliedM_of_G (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (d : mvcc.KBReal) (A' : List EntryModel) (ss : Loc) (bp : GoString) (γt : GName)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64) (lp al ast cl : Loc)
    (hany : E.authMode ≠ .any) :
    srvSnapAppliedG (GF := GF) E.authOn s ep sv γ ci E ρ γr d A' ss bp γt γn t c rs idm lp al
        ast cl ⊢
      srvSnapAppliedM E.authOn s ep sv γ ci E ρ γr d A' ss bp γt γn t c rs idm lp al ast cl := by
  cases hM : E.authMode with
  | any => exact absurd hM hany
  | off =>
    have hon : E.authOn = false := by simp [apply.AEnv.authOn, hM]
    rw [hon]
    exact srvSnapAppliedG_off s ep sv γ ci E ρ γr d A' ss bp γt γn t c rs idm lp al ast cl hM
  | on γa =>
    have hon : E.authOn = true := by simp [apply.AEnv.authOn, hM, auth.AuthMode.isOn]
    rw [hon]
    exact .rfl

end proof
end EtcdGrove
end Perennial
