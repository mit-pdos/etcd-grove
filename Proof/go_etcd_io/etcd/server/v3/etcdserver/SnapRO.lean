/-
**The server's snapshot path's persistent bundle and its boot resources** (D22 J1a, 2026-10-26;
`notes/snapshot-sj-plan.md`, "J1a" and "J0 decisions"; `notes/decisions.md`, "D22 J1a"). Lean-first.

`NewServer` makes, and `start`, `run` and `Start` thread (`isServerBuilt`, `isServerRun`), what the
apply thread's snapshot path (`applySnapshot.specSnap`, J8a) takes of the server's construction,
with the names it is stated over (`srvSnapBoot`):
* `srvSnapRO` (persistent): the configuration's fields the path reads (its logger, data
  directory, feature gate, quota and apply-duration warning), the snapshotter, the backend hooks
  over the consistent index, the raft storage over the snapshotter (`storage.storageSnap`, from
  `NewStorage`'s contract `rnNewStorageOk`), the member's snapshot directory's invariant at the
  names raft's names give the member (`SrvRaft.snapLoc`) with the server's removal fact
  `srvSnapRm` (J0 item 3), the stores and their contracts on whichever backend (the alarm store's,
  the auth store's in the environment's mode and, in the mode `off`, its `Recover`, the lessor's,
  the cluster's), the cluster's `Members()` (`srvMembersDir`, `bootOk`'s `Hmembers`), and the
  Key bucket's size bound of every backend at the boot parameters (`keySized`, `bootOk`'s);
* the snapshot-taken counter's authority at `0` (`γt`, the removal fact's);
* the reader-slot stocks `NewServer` dropped until J1a (`srvSnapStock`): the auth store's reader
  resource `E.RD` and `lgMu`'s reader slots, for the snapshots' `NewUberApplier` and `AddPeer`s.

Not here (J1a's findings, `notes/decisions.md`, "D22 J1a"): the whole configuration read-only
(`srvCfgAddr s ↦□ cfg`, which `applySnapshot` reads as a struct while `v3rpc.NewWatchServer` may
write its `WatchProgressNotifyInterval`, `issues/etcd-cfg-watch-progress-interval-race.md`), and
the meta reads of every backend (`specSnap`'s `isMetaBackend` family, false as stated for names the
backend was not opened with).

The stores' apply contracts (`alarmApplyOk`, `authApplyOkM`, `lessorApplyOk`, `clusterApplyOk`),
`memberDirIs`, `srvMembersDir` and `lessorLookupOk` moved here from `InvBoot.lean` and
`SnapApplyDefs.lean` (J1a), unchanged; `authRecoverOk` is S8d's `srvAuthRecoverOk`, renamed.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.etcd.server.v3.storage.InvHooks
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A member returned by `Members()`, its URLs the directory's** (D21 M2, 2026-10-19): owned
(`membership.memberIs`'s fields), with id `id`, its peer URLs `dir id`. -/
def memberDirIs (dir : w64 → List GoString) (m : Loc) (id : w64) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (pu cu : GoSlice) (il : Bool) (nm : GoString) (pus cus : List GoString),
    membership.mIDAddr m ↦ id ∗ membership.mPeerURLsAddr m ↦ pu ∗
    membership.mIsLearnerAddr m ↦ il ∗ membership.mNameAddr m ↦ nm ∗
    membership.mClientURLsAddr m ↦ cu ∗ pu ↦* pus ∗ cu ↦* cus ∗
    ⌜membership.peerURLsOk pus ∧ pus = dir id⌝)


/-- **The alarm store `a`'s apply contract on whichever backend it is on** (persistent; D22 receiver
epochs, S7c, 2026-10-23; `v3alarm.NewAlarmStore.spec`'s, the trust boundary): for a real backend
`d` (its contract at some `W`, `Pk`, its frozen post-lock hook `f`) and a write right `RW` lending
the tracked buckets' half of `d` and the store's user's half of `a.be` at an alarm backend over
`d` (`alarmBeOn`), the apply package's contract at `d`'s batch lock `Pk` and hook `f`. The user's
half, with the lock's (`alarmLockInv`), is what pins the store's writes to `d`, so the contract
stays true when `Recover` moves the store to another backend (the old user's half is gone, the new
one names the new backend; until S7c the contract was for `NewAlarmStore`'s backend only, false
once `Recover` runs). -/
def alarmApplyOk (a : Loc) : IProp GF :=
  iprop(□ ∀ (d : mvcc.KBReal) (W Pk : IProp GF) (γ : mvcc.StoreNames) (f : GoFunc) (RW : IProp GF),
    ⌜γ.kb = some d⌝ -∗ backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ rwLens RW iprop(srvRestRW d.γB ∗ alarmBeOn a d.be) -∗
    apply.isAlarmStore a γ Pk #f RW)

instance alarmApplyOk_persistent (a : Loc) : Persistent (alarmApplyOk (GF := GF) a) := by
  unfold alarmApplyOk; infer_instance

/-- **The auth store `stl`'s apply contract on whichever backend it is on, in the auth mode
`M`** (the auth plan's E2i, 2026-10-26; until then in the mode `off` only, `authApplyOk`): with
the store's verdicts in the mode `M`; the real store in the mode `on γa` meets it (`authApplyOkM_on`,
`AuthApplyOn.lean`; its admin clauses vacuous there, `apply.adminAdmitted`). -/
def authApplyOkM (M : auth.AuthMode) (stl : Loc) (RD : IProp GF) : IProp GF :=
  iprop(□ ∀ (d : mvcc.KBReal) (W Pk : IProp GF) (γ : mvcc.StoreNames) (f : GoFunc) (RW : IProp GF),
    ⌜γ.kb = some d⌝ -∗ backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ rwLens RW iprop(srvRestRW d.γB ∗ authBeOn stl d.be) -∗
    apply.isAuthStore (auth.authIface stl) γ Pk #f RD M RW)

/-- **The auth store `stl`'s apply contract on whichever backend it is on** (persistent; S7c;
`auth.NewAuthStore.spec`'s, the trust boundary), with the reader resource `RD`: as
`alarmApplyOk`, its writes pinned to the backend by the user's half of `st.be` (`authBeOn`). -/
def authApplyOk (stl : Loc) (RD : IProp GF) : IProp GF :=
  iprop(□ ∀ (d : mvcc.KBReal) (W Pk : IProp GF) (γ : mvcc.StoreNames) (f : GoFunc) (RW : IProp GF),
    ⌜γ.kb = some d⌝ -∗ backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ rwLens RW iprop(srvRestRW d.γB ∗ authBeOn stl d.be) -∗
    apply.isAuthStore (auth.authIface stl) γ Pk #f RD .off RW)

theorem authApplyOk_eq (stl : Loc) (RD : IProp GF) :
    authApplyOk (GF := GF) stl RD = authApplyOkM .off stl RD := rfl

instance authApplyOkM_persistent (M : auth.AuthMode) (stl : Loc) (RD : IProp GF) :
    Persistent (authApplyOkM (GF := GF) M stl RD) := by
  unfold authApplyOkM; infer_instance

/-- **The lessor `lp`'s backend contract on whichever backend it is on** (persistent; D22
receiver epochs, S7c; `lease.NewLessor.spec`'s, the trust boundary): as `alarmApplyOk`, its writes
pinned to the backend by the user's half of `le.b` (`lease.lessorBeOn`), which the write right
lends; one write-back token per write, the reader's open share lent. -/
def lessorApplyOk (lp : Loc) : IProp GF :=
  iprop(□ ∀ (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc) (RW : IProp GF),
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    rwLens RW iprop(srvRestRW d.γB ∗ lease.lessorBeOn lp d.be) -∗
    lease.lessorBackend lp Pk #f iprop(backend.wbTok d.γB ∗ RW) (mvcc.bkRTx d.γB d.P d.be))

instance lessorApplyOk_persistent (lp : Loc) : Persistent (lessorApplyOk (GF := GF) lp) := by
  unfold lessorApplyOk; infer_instance

/-- **The cluster `c`'s apply contract on whichever backend it is on** (persistent; D22 receiver
epochs, S7e, 2026-10-23; `bootOk`'s, the bootstrap contract): for a real backend `d` (its
contract at some `W`, `Pk`, its frozen post-lock hook `f`), the apply package's `isCluster` at `d`'s
batch lock `Pk` and hook `f`, given a rest resource `RO` lending the backend's tracked buckets'
half and the cluster's in-memory members with its `be` field at a membership backend over `d`
(`clusterBeOn`, `roLens`), and a write right `RW` lending the half and the field (`rwLens`). The
field (`c.be`: no lock guards it, the apply thread is its only reader and writer) pins the
cluster's writes to `d`; `SetBackend` replaces it. Until S7e the contract was for the boot
backend's batch lock only, false once `applySnapshot` calls `SetBackend`. -/
def clusterApplyOk (c : Loc) : IProp GF :=
  iprop(□ ∀ (d : mvcc.KBReal) (W Pk : IProp GF) (γ' : mvcc.StoreNames) (f : GoFunc)
      (RO : apply.RestM → IProp GF) (RW : IProp GF),
    ⌜γ'.kb = some d⌝ -∗ backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ (∃ n : Loc, membership.rcVersionChangedAddr c ↦□ n) -∗
    roLens RO (fun r => iprop(srvRestOwn d.γB c r ∗ clusterBeOn c d.be)) -∗
    rwLens RW iprop(srvRestRW d.γB ∗ clusterBeOn c d.be) -∗
    apply.isCluster c γ' Pk #f RO RW)

instance clusterApplyOk_persistent (c : Loc) : Persistent (clusterApplyOk (GF := GF) c) := by
  unfold clusterApplyOk; infer_instance

instance authApplyOk_persistent (stl : Loc) (RD : IProp GF) :
    Persistent (authApplyOk (GF := GF) stl RD) := by
  unfold authApplyOk; infer_instance


/-- **The auth store `ast`'s `Recover` on a new backend** (persistent; D22 J1a, 2026-10-26: the
body of S8d's named premise `srvAuthRecoverOk`, moved beside the stores' apply contracts and given by
`auth.NewAuthStore.spec`, the trust boundary, in its mode `off`): for any later backend `dn` with its
contract, an open share, a reader token and its tracked buckets with the auth buckets at
`authBoot`/empty, `Recover(ab)` moves the store's user's half `authBeOn ast oldbe` to the new
backend, all else given back. -/
def authRecoverOk (ast : Loc) : IProp GF :=
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

instance authRecoverOk_persistent (ast : Loc) : Persistent (authRecoverOk (GF := GF) ast) := by
  unfold authRecoverOk; infer_instance

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

/-- The lessor `lp`'s `Lookup` (`lease.NewLessor.spec`'s, the trust boundary; S8d's named premise,
threaded from `NewServer`): what `isApplyLessor_of_lessorInv` takes. -/
def lessorLookupOk (lp : Loc) : IProp GF :=
  iprop(□ (∀ id : w64,
    {{ True }} (App (Val (lp @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.lease.lessor.ty @!! go!"Lookup")) (Val #id))
    {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ apply.leaseIs l id }}))

instance lessorLookupOk_persistent (lp : Loc) : Persistent (lessorLookupOk (GF := GF) lp) := by
  unfold lessorLookupOk; infer_instance

/-- **The removal fact of the server's snapshot directory** (D22 J0 item 3, J1a; `snapDirInv`'s
`Rm`): a `.snap.db` file of index `j` may be gone once a snapshot at `j` or above was opened
(`snapTakenLb γt j`: `applySnapshot(i)`'s own `Release`, after the open, removes the files below
`i`) or the apply thread has applied past `j` (`γr.applied` at least `j + 1`, as a natural number:
`snapshot`'s `Release` at the applied index removes files saved but never opened). Both are
refuted for the file `applySnapshot(i)` opens, with the apply thread's authorities (`γt` at most its
applied index, which is below `i`). Supersedes S8d's `snapTakenLb γt`. -/
def srvSnapRm (γt : GName) (γr : ReadNames) (j : w64) : IProp GF :=
  iprop(snapTakenLb γt j ∨ monoNatLbOwn γr.applied (uint.nat j + 1))

instance srvSnapRm_persistent (γt : GName) (γr : ReadNames) (j : w64) :
    Persistent (srvSnapRm (GF := GF) γt γr j) := by
  unfold srvSnapRm; infer_instance

/-- **The snapshot path's persistent bundle** (see the file header) of the server `s` with the
consistent index `ci`, the apply environment `E` and the read names `γr`, the snapshot-taken
counter `γt`. -/
def srvSnapRO (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γt : GName) : IProp GF :=
  iprop(□ ∃ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk lgh stp : Loc) (γd : GName)
      (idm : w64) (al ast lp cl : Loc) (ps : List w64) (dir : w64 → List GoString)
      (d : mvcc.KBReal),
    ⌜E.γ.kb = some d ∧ cfg.Logger' ≠ null ∧ storage.storageSnap stp ss ∧ storage.dbOpensOk ∧
      apply.backendUnderQuota ∧ γr.raft.raft.snapLoc idm = some γd ∧
      (∀ f, dir f ≠ [] ↔ f ∈ ps)⌝ ∗
    -- the configuration's fields the snapshot path reads, its feature gate
    srvCfgFieldAddr s go!"Logger" ↦□ cfg.Logger' ∗ srvCfgFieldAddr s go!"DataDir" ↦□ cfg.DataDir' ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ cfg.ServerFeatureGate' ∗
    isFeatureGate cfg.ServerFeatureGate' ∗
    srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ cfg.QuotaBackendBytes' ∗
    srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ cfg.WarningApplyDuration' ∗
    -- the snapshotter, the backend hooks over the consistent index, the storage over the snapshotter
    structFieldRef EtcdServer go!"snapshotter" s ↦□ ss ∗ snap.isSnapshotter ss ∗
    structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
    storage.isBackendHooks hk
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩ lgh ∗
    rnStorageAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.storage.ty) #stp : GoInterface) ∗
    -- the member's snapshot directory, at raft's names for the member (D22 J2)
    srvMemberIDAddr s ↦□ idm ∗
    inv snapDirN (snapDirInv ss γd (srvImage γr.raft.raft) (srvSnapRm γt γr)) ∗
    -- the stores and their contracts on whichever backend
    srvAlarmStoreAddr s ↦□ al ∗ srvAuthStoreAddr s ↦□ auth.authIface ast ∗
    srvLessorAddr s ↦□ lease.lessorIface lp ∗ srvClusterAddr s ↦□ cl ∗
    isAlarmStore al ∗ alarmApplyOk al ∗ authApplyOkM E.authMode ast E.RD ∗
    □ (⌜E.authMode = auth.AuthMode.off⌝ → authRecoverOk ast) ∗
    lessorApplyOk lp ∗ lease.lessorCfg lp ∗ lessorLookupOk lp ∗
    membership.isRaftCluster cl ∗ clusterApplyOk cl ∗
    (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ∗ srvMembersDir cl ps dir ∗
    -- the Key bucket's size bound of every backend at the boot parameters
    □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b))

instance srvSnapRO_persistent (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γt : GName) :
    Persistent (srvSnapRO (GF := GF) s ci E γr γt) := by
  unfold srvSnapRO; infer_instance

/-- **The reader-slot stocks** (see the file header; spatial): `n` of the auth store's reader
resource and `m` of `lgMu`'s reader slots, at least `2 ^ 28` each. -/
def srvSnapStock (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ n m : Nat, ⌜2 ^ 28 ≤ n ∧ 2 ^ 28 ≤ m⌝ ∗
    ([∗list] _x ∈ List.replicate n (), E.RD) ∗ ([∗list] _x ∈ List.replicate m (), srvLgReader s))

/-- **What `NewServer` hands the snapshot path** (see the file header): the bundle at a fresh
snapshot-taken counter, its authority at `0`, the stocks. -/
def srvSnapBoot (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ γt : GName, srvSnapRO s ci E γr γt ∗ monoNatAuthOwn γt 1 0 ∗ srvSnapStock s E)

end defs

end EtcdGrove
end Perennial
