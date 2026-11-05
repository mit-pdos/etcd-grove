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
* (until J8a-6, 2026-11-01) a reader-slot stock (`srvSnapStock`): `lgMu`'s reader slots for the
  snapshots' `AddPeer`s (and until J8a-1 the auth store's reader resource `E.RD`, which the
  snapshots' `NewUberApplier` took until the auth layer's `Apply` borrowed its caller's). Gone: the
  transport's peers borrow from its thread pool (`raftPool`), so an `AddPeer` takes no slot.

The whole configuration read-only (`srvCfgAddr s ↦□ cfg`, which `applySnapshot` reads as a
struct) is the bundle's last conjunct, a rebuild from the two fields `start` writes (J8a-3,
2026-11-01: the fork's `NewWatchServer` no longer writes the configuration,
`nonissues/etcd-cfg-watch-progress-interval-race.md`; `isServerRun`'s `"#Hsncfg"` holds the fields).
Not here (J1a's findings, `notes/decisions.md`, "D22 J1a"): the meta reads of every backend
(`specSnap`'s `isMetaBackend` family, false as stated for names the backend was not opened with;
J8a-4).

The stores' apply contracts (`alarmApplyOk`, `authApplyOkM`, `lessorApplyOk`, `clusterApplyOk`),
(Strict M1, 2026-11-06.) Over mvcc's API: a backend is a `BkRef` (`d.γB`, `d.P`, `d.b`), the
stores' contracts at the backend tie `srvBkTie d` and the batch lock's invariant `Pk` of every
backend of the epoch (`fun _ => Pk`) in place of the store's names `γ` with `γ.kb = some d`; the
backend's compaction mode and the store's watch flag gone (the API's backend always compacts, its
store has one form), the KV a store handle (`□ isMvcc kv E.γ`), the lessor at the store's lessor
names (`mvccLeases E.γ`); the KV's closer (`srvKVCloser`, `srvKVCloserW`) deleted: what `Restore`
takes of the store, mvcc's open token `mvccOpen`, is the apply thread's (`apply.cmpOwn`).

`memberDirIs`, `srvMembersDir` and `lessorLookupOk` moved here from `InvBoot.lean` and
`SnapApplyDefs.lean` (J1a), unchanged (`memberDirIs` and `srvMembersDir` moved on to
`InvApRes.lean`, 2026-11-01, for `ccMembRes`); `authRecoverOk` is S8d's `srvAuthRecoverOk`, renamed.
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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.config.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open mvcc.api (BkRef isMvcc mvccLeases)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


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
  iprop(□ ∀ (d : BkRef) (W Pk : IProp GF) (f : GoFunc) (RW : IProp GF),
    backend.isBackend d.γB d.P W Pk d.b -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ rwLens RW iprop(srvRestRW d.γB ∗ alarmBeOn a d.b) -∗
    apply.isAlarmStore a (fun _ => Pk) f (srvBkTie d) RW)

instance alarmApplyOk_persistent (a : Loc) : Persistent (alarmApplyOk (GF := GF) a) := by
  unfold alarmApplyOk; infer_instance

/-- **The auth store `stl`'s apply contract on whichever backend it is on, in the auth mode
`M`** (the auth plan's E2i, 2026-10-26; until then in the mode `off` only, `authApplyOk`): with
the store's verdicts in the mode `M`; the real store in the mode `on γa` meets it (`authApplyOkM_on`,
`AuthApplyOn.lean`; its admin clauses vacuous there, `apply.adminAdmitted`). -/
def authApplyOkM (M : auth.AuthMode) (stl : Loc) (RD : IProp GF) : IProp GF :=
  iprop(□ ∀ (d : BkRef) (W Pk : IProp GF) (f : GoFunc) (RW : IProp GF),
    backend.isBackend d.γB d.P W Pk d.b -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ rwLens RW iprop(srvRestRW d.γB ∗ authBeOn stl d.b) -∗
    apply.isAuthStore (auth.authIface stl) (fun _ => Pk) f (srvBkTie d) RD M RW)

/-- **The auth store `stl`'s apply contract on whichever backend it is on** (persistent; S7c;
`auth.NewAuthStore.spec`'s, the trust boundary), with the reader resource `RD`: as
`alarmApplyOk`, its writes pinned to the backend by the user's half of `st.be` (`authBeOn`). -/
def authApplyOk (stl : Loc) (RD : IProp GF) : IProp GF :=
  iprop(□ ∀ (d : BkRef) (W Pk : IProp GF) (f : GoFunc) (RW : IProp GF),
    backend.isBackend d.γB d.P W Pk d.b -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ rwLens RW iprop(srvRestRW d.γB ∗ authBeOn stl d.b) -∗
    apply.isAuthStore (auth.authIface stl) (fun _ => Pk) f (srvBkTie d) RD .off RW)

theorem authApplyOk_eq (stl : Loc) (RD : IProp GF) :
    authApplyOk (GF := GF) stl RD = authApplyOkM .off stl RD := rfl

instance authApplyOkM_persistent (M : auth.AuthMode) (stl : Loc) (RD : IProp GF) :
    Persistent (authApplyOkM (GF := GF) M stl RD) := by
  unfold authApplyOkM; infer_instance

/-- **The lessor `lp`'s backend contract on whichever backend it is on** (persistent; D22
receiver epochs, S7c; `lease.NewLessor.spec`'s, the trust boundary): as `alarmApplyOk`, its writes
pinned to the backend by the user's half of `le.b` (`lease.lessorBeOn`), which the write right
lends; one write-back token per write, the reader's open share lent; the put into `Lease` (a
tracked bucket, D22) with the lease bucket's part (`backend.rbPart d.γB (· = "lease")`, per bucket:
the lessor's put writes `Lease` only; 2026-11-01, the backend-auth-split stage: until then the
whole client half `backend.rbOwn`), given back with the record put (leases T3, L3c, 2026-10-27:
until then the write right lent the half, `srvRestRW`, and the put's effect was not stated; the
real backend's `LockInsideApply` does not need it, its `UnsafePut` does). -/
def lessorApplyOk (lp : Loc) : IProp GF :=
  iprop(□ ∀ (d : BkRef) (W Pk : IProp GF) (f : GoFunc) (RW : IProp GF),
    backend.isBackend d.γB d.P W Pk d.b -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    rwLens RW (lease.lessorBeOn lp d.b) -∗
    lease.lessorBackend lp Pk #f iprop(backend.wbTok d.γB ∗ RW) (apply.bkRT d)
      (backend.rbPart d.γB (· = go!"lease")))

instance lessorApplyOk_persistent (lp : Loc) : Persistent (lessorApplyOk (GF := GF) lp) := by
  unfold lessorApplyOk; infer_instance

/-- The server's write right holds the lessor's write token's part (its half of `le.b`) and the
lease bucket's part of the tracked buckets' client half, the right its put takes (leases T3, L3c,
2026-10-27; the lease bucket's part since 2026-11-02, the backend-auth-split stage, as
`lessorApplyOk` now takes it). -/
theorem srvRestRWH_lessor [go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ □ (srvRestRWH (GF := GF) γB (srvObjsOn al ast lp cl be) -∗
      lease.lessorBeOn lp be ∗ ∃ r, backend.rbPart γB (· = go!"lease") r) := by
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, -, -, Hle, -⟩
  iunfold srvRestRW at Hrw
  icases Hrw with ⟨%r, Hrw, -⟩
  ihave ⟨Hrw, -⟩ := (backend.rbOwn_split (GF := GF) γB (fun n : GoString => n = go!"lease") r).1 $$ Hrw
  iframe Hle
  iexists r
  iexact Hrw

/-- The lessor's write token's part lends itself. -/
theorem lessorBeOn_lens (lp be : Loc) :
    ⊢ rwLens (GF := GF) (lease.lessorBeOn lp be) (lease.lessorBeOn lp be) := by
  iunfold rwLens
  iintro !> Hle
  iframe Hle
  iintro Hle; iexact Hle

/-- The `Lease` bucket is not one of the cluster's (2026-11-02, the backend-auth-split stage). -/
theorem lease_not_clusterBkts : ¬ membership.clusterBkts mvcc.leaseName := by
  simp [membership.clusterBkts, membership.memberBkts, mvcc.leaseName,
    go_etcd_io.etcd.server.v3.storage.schema.leaseName]

/-- **The server's rest resource lends the lessor's revocation its buckets** (the lease-revoke
plan, 2026-10-31; `apply.isApplyLessor_of_lessorInv`'s lens): at the store's real backend `d` (its
parameters naming the `Lease` bucket, tracked, with no hook keys: `leaseParams`, a boot fact), the
`Lease` bucket's part (`rbPart`, with the parameters' `leaseParams`: what `lessor.Revoke.spec` takes;
strict M1, 2026-11-06: until then mvcc's `storeRb`, the same) and the lessor's half of `le.b`, given back at
any buckets agreeing with the model's off `lease`. (2026-11-02, the backend-auth-split stage: the
part of `Lease`, split off `srvRestOwn`'s part of the non-cluster buckets; until then the whole
client half, given back at any buckets.) -/
theorem srvRestOwnH_lens_revoke [go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    (d : BkRef) (hlp : mvcc.leaseParams d.P) (al ast lp cl : Loc) :
    ⊢ □ (∀ rs : apply.RestM, srvRestOwnH (GF := GF) d.γB cl (srvObjsOn al ast lp cl d.b) rs -∗
      backend.rbPart d.γB (· = mvcc.leaseName) rs.bk ∗ ⌜mvcc.leaseParams d.P⌝ ∗
        lease.lessorBeOn lp d.b ∗
        (∀ bk, ⌜∀ n, n ≠ mvcc.leaseName → bk.lookup n = rs.bk.lookup n⌝ -∗
          ⌜(rs.bk.lookup mvcc.leaseName).isSome → (bk.lookup mvcc.leaseName).isSome⌝ -∗
          backend.rbPart d.γB (· = mvcc.leaseName) bk ∗ lease.lessorBeOn lp d.b -∗
          srvRestOwnH d.γB cl (srvObjsOn al ast lp cl d.b) { rs with bk := bk })) := by
  have hlc := lease_not_clusterBkts
  have hset : ∀ n, (¬ membership.clusterBkts n) ↔
      (n = mvcc.leaseName ∨ (¬ membership.clusterBkts n ∧ n ≠ mvcc.leaseName)) := by
    intro n
    by_cases h : n = mvcc.leaseName
    · subst h; exact ⟨fun _ => Or.inl rfl, fun _ => hlc⟩
    · exact ⟨fun hc => Or.inr ⟨hc, h⟩, fun hx => hx.elim (fun e => absurd e h) And.left⟩
  have hd : ∀ n, n = mvcc.leaseName →
      (¬ membership.clusterBkts n ∧ n ≠ mvcc.leaseName) → False := fun _ h1 h2 => h2.2 h1
  iintro !> %rs Hro
  iunfold srvRestOwnH at Hro
  iunfold srvObjsOn at Hro
  icases Hro with ⟨Hro, Hal, Hau, Hle, Hcb⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hcl, Hnc, Hmem, %Hmi⟩
  ihave Hnc := (backend.rbPart_set (GF := GF) d.γB _ _ rs.bk hset).1 $$ Hnc
  icases (backend.rbPart_split (GF := GF) d.γB (· = mvcc.leaseName)
    (fun n => ¬ membership.clusterBkts n ∧ n ≠ mvcc.leaseName) rs.bk hd).1 $$ Hnc with ⟨Hl, Hnc⟩
  iframe Hl Hle
  isplitr
  · ipureintro; exact hlp
  iintro %bk %hbk %hl ⟨Hl, Hle⟩
  iunfold srvRestOwnH
  iunfold srvObjsOn
  iunfold srvRestOwn
  iframe Hmem Hal Hau Hle Hcb
  isplitl [Hcl]
  · iapply (backend.rbOwnIn_congr (GF := GF) d.γB _ rs.bk bk
      (fun n hn => (hbk n (fun e => hlc (e ▸ hn))).symm)).1 $$ Hcl
  isplitl [Hl Hnc]
  · iapply (backend.rbPart_set (GF := GF) d.γB _ _ bk hset).2
    iapply (backend.rbPart_split (GF := GF) d.γB (· = mvcc.leaseName)
      (fun n => ¬ membership.clusterBkts n ∧ n ≠ mvcc.leaseName) bk hd).2
    iframe Hl
    iapply (backend.rbPart_congr (GF := GF) d.γB _ rs.bk bk (fun n hn => (hbk n hn.2).symm)).1 $$ Hnc
  · ipureintro; exact ⟨Hmi.1, restPresent_lens _ _ hbk hl Hmi.2⟩

/-- **The cluster `c`'s apply contract on whichever backend it is on** (persistent; D22 receiver
epochs, S7e, 2026-10-23; `bootOk`'s, the bootstrap contract): for a real backend `d` (its
contract at some `W`, `Pk`, its frozen post-lock hook `f`), the apply package's `isCluster` at `d`'s
batch lock `Pk` and hook `f`, given a rest resource `RO` lending the backend's tracked buckets'
half and the cluster's in-memory members with its `be` field at a membership backend over `d`
(`clusterBeOn`, `roLens`), and a write right `RW` lending the half and the field (`rwLens`). The
field (`c.be`: no lock guards it, the apply thread is its only reader and writer) pins the
cluster's writes to `d`; `SetBackend` replaces it. Until S7e the contract was for the boot
backend's batch lock only, false once `applySnapshot` calls `SetBackend`. (2026-11-01, the
backend-auth-split stage: the rest resource holds the cluster's buckets idle. True of the Go code:
`SetVersion`'s `MustSaveClusterVersionToBackend` and `UpdateAttributes`' `MustSaveMemberToBackend`
lock the batch (`LockInsideApply`), put, and `Unlock`, which writes the put back, the Go basis;
without `shouldApplyV3` they write nothing; so after either, the readers see the writer's contents
on the cluster's buckets, `TestBks2WriterAnySIdle`. `UpdateAttributes` saves under
`BackendMemberKey(m.ID)`, which is the model's `memberKey a.memberID` because `srvRestOwn` holds
`memIdOk`, kept by both rows (`restModel_memIdOk`'s steps).) (2026-11-02, the cluster-rows stage:
the rows' premises, the version not above the server's and `UpdateAttributes`' member in `r.mem`,
`SetVersion`'s callback fixed with its package initializations; the rest resource and the write
right hold the rest buckets present, and the members' client URLs are read-only. Until then the
rows claimed a return where Go panics or is fatal; they still do above bbolt's `MaxValueSize`, as
`isCluster` says.) -/
def clusterApplyOk (c : Loc) : IProp GF :=
  iprop(□ ∀ (d : BkRef) (W Pk : IProp GF) (f : GoFunc)
      (RO : apply.RestM → IProp GF) (RW : IProp GF),
    backend.isBackend d.γB d.P W Pk d.b -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ (∃ n : Loc, membership.rcVersionChangedAddr c ↦□ n) -∗
    roLens RO (fun r => iprop(srvRestOwn d.γB c r ∗ clusterBeOn c d.b)) -∗
    rwLens RW iprop(srvRestRW d.γB ∗ clusterBeOn c d.b) -∗
    apply.isCluster c (fun _ => Pk) f (srvBkTie d) RO RW)

instance clusterApplyOk_persistent (c : Loc) : Persistent (clusterApplyOk (GF := GF) c) := by
  unfold clusterApplyOk; infer_instance

instance authApplyOk_persistent (stl : Loc) (RD : IProp GF) :
    Persistent (authApplyOk (GF := GF) stl RD) := by
  unfold authApplyOk; infer_instance


/-- **The auth store `ast`'s `Recover` on a new backend** (persistent; D22 J1a, 2026-10-26: the
body of S8d's named premise `srvAuthRecoverOk`, moved beside the stores' apply contracts and given by
`auth.NewAuthStore.spec`, the trust boundary, in its mode `off`): for any later backend `dn` with its
contract, an open share, a pooled reader's resource and the caller's thread token
(`backend.bkRPool`, `threadTok`), and **the idle part of its auth buckets** at `authBoot`/empty
(`rbOwnIn dn.γB auth.authBkts r`, what `Recover`'s read transaction sees: the Go basis),
`Recover(ab)` moves the store's user's half `authBeOn ast oldbe` to the new backend, all else given
back. (2026-11-02, the backend-auth-split stage: until then the reader's token and open share
`mvcc.bkRTx` and the writer's half `rbOwn`, with `authRoles` empty too; `NewAuthStore.spec`'s last
two bullets say why.) -/
def authRecoverOk (ast : Loc) : IProp GF :=
  iprop(□ (∀ (oldbe abl lg : Loc) (dn : BkRef) (W Pk : IProp GF) (qo : Qp)
          (r : GMap GoString backend.BktData),
        {{ authBeOn ast oldbe ∗ ⌜lg ≠ null⌝ ∗
            structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
              (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
                #dn.b : GoInterface) ∗
            structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg ∗
            backend.isBackend dn.γB dn.P W Pk dn.b ∗ backend.bOpen dn.γB qo ∗
            backend.bkRPool dn.γB dn.P dn.b ∗ threadTok ∗ backend.rbOwnIn dn.γB auth.authBkts r ∗
            ⌜(r.lookup go!"auth").getD ∅ = authBoot ∧ (r.lookup go!"authUsers").getD ∅ = ∅⌝ }}
          (App (Val (ast @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
            go!"Recover")) (Val #(authBkIface abl)))
        {{ RET #(); authBeOn ast dn.b ∗ backend.bOpen dn.γB qo ∗ backend.bkRPool dn.γB dn.P dn.b ∗
            threadTok ∗ backend.rbOwnIn dn.γB auth.authBkts r }}))

instance authRecoverOk_persistent (ast : Loc) : Persistent (authRecoverOk (GF := GF) ast) := by
  unfold authRecoverOk; infer_instance

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

/-- (2026-11-01, J8a-5) **The snapshot's file taken from the directory** (`applyAll`'s, before
`applySnapshot(i)`, whose `OpenSnapshotBackend` renames it): a saved index `i` above the counter's
`nt` and the applied index `a` is present, its removal fact (`srvSnapRm γt γr i`) refuted by the
apply thread's authorities; the counter raised to `i` gives that fact, so the file leaves the
directory, with its certificate. A later credit strips the invariant's later (`fileHolds` is not
timeless). -/
theorem snapDir_take (ss : Loc) (γd γt : GName) (γr : ReadNames)
    (img : w64 → backend.Data → IProp GF) (i a : w64) (nt : Nat) (hnt : nt < uint.nat i)
    (ha : uint.Z a < uint.Z i) :
    ⊢ £ 1 -∗ inv snapDirN (snapDirInv ss γd img (srvSnapRm γt γr)) -∗ snapSaved γd i -∗
      monoNatAuthOwn γt 1 nt -∗ srvAppliedOwn γr a ={⊤}=∗
      monoNatAuthOwn γt 1 (uint.nat i) ∗ srvAppliedOwn γr a ∗
      ∃ D : backend.Data, backend.fileHolds (snap.snapDBPath ss i) D ∗ □ img i D := by
  iintro Hlc #Hinv #Hsv Hγt Hao
  iinv Hinv with Hi Hclose
  imod (lc_fupd_elim_later (P := snapDirInv ss γd img (srvSnapRm γt γr))) $$ Hlc Hi with Hi
  iunfold snapDirInv at Hi
  icases Hi with ⟨%M, %Es, Ha, %HME, HM, #HEs, #HRm⟩
  iunfold snapSaved at Hsv
  ihave %HEi := ghost_map_lookup $$ Ha Hsv
  cases hMi : M.lookup i with
  | none =>
    have hp : Es.lookup i ≠ none ∧ M.lookup i = none := ⟨by simp [HEi], hMi⟩
    ihave #Hr := HRm $$ %i %hp
    iunfold srvSnapRm at Hr
    icases Hr with (#Hr | #Hr)
    · iunfold snapTakenLb at Hr
      ihave %Hv := monoNatLbOwn_valid γt 1 nt (uint.nat i) $$ Hγt Hr
      exfalso; omega
    · iunfold srvAppliedOwn at Hao
      icases Hao with ⟨Hao1, -⟩
      ihave %Hv := monoNatLbOwn_valid γr.applied _ _ _ $$ Hao1 Hr
      exfalso; have := Hv.2; word
  | some D =>
    imod (mono_nat_own_update (uint.nat i) (by omega)) $$ Hγt with ⟨Hγt, #Htk⟩
    icases (BigSepM.bigSepM_delete (Φ := fun (j : w64) (D : backend.Data) => iprop(backend.fileHolds
      (snap.snapDBPath ss j) D ∗ □ img j D)) hMi).1 $$ HM with ⟨⟨Hf, #Himg⟩, HM⟩
    imod Hclose $$ [Ha HM] with -
    · inext
      iunfold snapDirInv
      iexists GMap.delete i M, Es
      iframe Ha HM HEs
      isplitr
      · ipureintro
        intro j hj
        by_cases hji : i = j
        · subst hji; exact absurd (GMap.lookup_delete M i) hj
        · rw [GMap.lookup_delete_ne M hji] at hj; exact HME j hj
      iintro !> %j %hj
      by_cases hji : i = j
      · subst hji
        iunfold srvSnapRm; ileft; iunfold snapTakenLb; iexact Htk
      · rw [GMap.lookup_delete_ne M hji] at hj
        iapply HRm $$ %j %hj
    imodintro
    iframe Hγt Hao
    iexists D
    iframe Hf Himg

/-- **The snapshot path's persistent bundle** (see the file header) of the server `s` with the
consistent index `ci`, the apply environment `E` and the read names `γr`, the snapshot-taken
counter `γt`. -/
def srvSnapRO (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γt : GName) : IProp GF :=
  iprop(□ ∃ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk lgh stp : Loc) (γd : GName)
      (idm : w64) (al ast lp cl : Loc) (ps : List w64) (dir : w64 → List GoString)
      (d : BkRef),
    ⌜E.BkTie = srvBkTie d ∧ cfg.Logger' ≠ null ∧ storage.storageSnap stp ss ∧ storage.dbOpensOk ∧
      storage.openMmapOk cfg ∧
      apply.backendUnderQuota ∧ γr.raft.raft.snapLoc idm = some γd ∧
      (∀ f, dir f ≠ [] ↔ f ∈ ps) ∧
      -- (2026-11-01, J8a-1, item 7) the environment's facts `specSnap` takes: the snapshot files'
      -- opens, the backend's parameters, the rest buckets' resource at this backend, the receipts'
      -- bound (strict M1: the backend's compaction mode and the store's watch flag gone)
      storage.snapOpensOk ∧ mvcc.bridgeParams d.P ∧ ciKeys d.P ∧
      storage.hooksParams d.P ∧ d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ mvcc.leaseParams d.P ∧
      -- (2026-11-02, the backend-auth-split stage) the alarm bucket in the table, which the alarm
      -- store's `Recover` takes (`bootOk`'s)
      d.P.has mvcc.alarmBI ∧
      E.RO = srvRestOwnH d.γB cl (srvObjsOn al ast lp cl d.b) ∧
      receiptBound GF ≤ backend.wbInit - 6⌝ ∗
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
    □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗
    -- (2026-11-01, J8a-1, item 7) the lessor's invariant, the KV the store's handle (strict M1:
    -- `□ isMvcc`, as the reader's view; until then the watchable store)
    lease.lessorInv lp (mvccLeases E.γ) ∗
    (srvKVAddr s ↦□ E.kv ∗ □ isMvcc E.kv E.γ) ∗
    -- (J8a-3, 2026-11-01) **the configuration's rebuild**: the whole struct read-only at `cfg` but
    -- for the two fields `start` writes (`SnapshotCount`, `SnapshotCatchUpEntries`), from those
    -- read-only (`isServerRun`'s `"#Hsncfg"`, which `start` persists): `applySnapshot.specSnap`'s
    -- `srvCfgAddr s ↦□ cfg'` (its struct copy `OpenSnapshotBackend(s.Cfg, …)`)
    □ (∀ (sc scu : w64), srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc -∗
      srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu -∗
      srvCfgAddr s ↦□ ({ cfg with SnapshotCount' := sc, SnapshotCatchUpEntries' := scu } :
        go_etcd_io.etcd.server.v3.config.ServerConfig)))

instance srvSnapRO_persistent (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γt : GName) :
    Persistent (srvSnapRO (GF := GF) s ci E γr γt) := by
  unfold srvSnapRO; infer_instance

/-- (2026-11-01, J8a-1, item 7) **The auth store's contract mode off, from auth off**: `authOn` is the
mode's `isOn`, which only `.off` is not (`specSnap`'s `hoff` from the run's `authOn = false`). -/
theorem authMode_off_of (E : apply.AEnv GF) (h : E.authOn = false) : E.authMode = auth.AuthMode.off := by
  unfold apply.AEnv.authOn at h
  cases hm : E.authMode <;> simp_all [auth.AuthMode.isOn]

/-- (2026-11-01, J8a-1, item 5) **The bundle at the next backend**: `srvSnapRO` at the environment
`E'` a snapshot install moves to (`beSucc`: the store's handle and names, the auth store's reader
resource and mode kept), from the new backend's facts `srvSnapApplied` gives (`E'` on `d'`, at the
boot parameters, the rest buckets' resource at it) and the stores' addresses, which name the
bundle's. (Strict M1, 2026-11-06: the backends `BkRef`s, named by the environments' ties.) -/
theorem srvSnapRO_succ {γ γ' : ApplyNames} {E E' : apply.AEnv GF} (s ci : Loc) (γr : ReadNames)
    (γt : GName) (d d' : BkRef) (al ast lp cl : Loc)
    (hb : beSucc γ E γ' E') (hkb : E.BkTie = srvBkTie d) (hkb' : E'.BkTie = srvBkTie d')
    (hP : d'.P = d.P)
    (hRO : E'.RO = srvRestOwnH d'.γB cl (srvObjsOn al ast lp cl d'.b)) :
    srvSnapRO s ci E γr γt ∗ srvAlarmStoreAddr s ↦□ al ∗ srvAuthStoreAddr s ↦□ auth.authIface ast ∗
      srvLessorAddr s ↦□ lease.lessorIface lp ∗ srvClusterAddr s ↦□ cl ⊢
    srvSnapRO s ci E' γr γt := by
  obtain ⟨-, b, P, f, c, RO, RW, rfl⟩ := hb
  iintro ⟨#H, #Hal, #Hau, #Hle, #Hcl⟩
  iunfold srvSnapRO at H
  icases H with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al0, %ast0, %lp0, %cl0, %ps, %dir, %d0,
    %Hp, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11, #H12, #H13, #H14, #H15, #H16, #H17,
    #H18, #H19, #H20, #H21, #H22, #H23, #H24, #H25, #H26, #H27, #H28, #H29, #H30, #H31⟩
  icombine Hal H14 gives %e1
  icombine Hau H15 gives %e2
  icombine Hle H16 gives %e3
  icombine Hcl H17 gives %e4
  simp only [auth.authIface, lease.lessorIface, interface_mkOk_inj] at e2 e3
  obtain ⟨hkb0, hlg, hstp, hdbo, hmm, hbuq, hsl, hdir, hsop, hbr, hci, hhk, hwf, hlim, hlp, halbi,
    -, hrb⟩ := Hp
  rw [hkb] at hkb0
  obtain rfl := srvBkTie_inj d d0 hkb0
  have e2' : ast = ast0 := by
    simp only [intoVal_eq_iff, true_and] at e2; first | exact e2 | exact e2.symm
  have e3' : lp = lp0 := by
    simp only [intoVal_eq_iff, true_and] at e3; first | exact e3 | exact e3.symm
  subst al0 cl0 ast0 lp0
  iunfold srvSnapRO
  imodintro
  iexists cfg, ss, hk, lgh, stp, γd, idm, al, ast, lp, cl, ps, dir, d'
  isplitr
  · ipureintro
    refine ⟨hkb', hlg, hstp, hdbo, hmm, hbuq, hsl, hdir, hsop, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hRO, hrb⟩ <;> rw [hP] <;> assumption
  have e5 : (E.onBe b P f c RO RW).authMode = E.authMode := rfl
  have e6 : (E.onBe b P f c RO RW).RD = E.RD := rfl
  have e7 : (E.onBe b P f c RO RW).γ = E.γ := rfl
  have e8 : (E.onBe b P f c RO RW).kv = E.kv := rfl
  rw [e5, e6, e7, e8, hP]
  iframe #

/-- **The snapshot path's own resources at the current backend** (D22 J1b, 2026-10-31; spatial):
what `applySnapshot.specSnap` takes of the backend `E` is on (`E.γ.kb = some d`) and gives back at
the new one (`srvSnapApplied`): the backend's stop channels and the constructors' half of its open
token (W7: the old backend's `Close` goroutine takes them), the alarm store's field (until
2026-11-01, J8a-5, also its `Get` under a resource `Tal`, `zal`: `specSnap` now gets `Get` with no
alarm from `Recover`'s `alarmEmpty`); and the backend file's directory entry at the configuration's
data directory (`pathOwn (backendPathOf dd)`, `OpenSnapshotBackend`'s rename target, one for every
install). (Until strict M1, 2026-11-06, also the KV's closer, `srvKVCloserW`, for `store.Restore`:
over the API, `Restore` takes mvcc's open token, the apply thread's `apply.cmpOwn`.) -/
def srvSnapRes (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ (d : BkRef) (al : Loc) (dd : GoString),
    ⌜E.BkTie = srvBkTie d⌝ ∗
    backend.isStopChans d.γB d.b ∗ backend.bOpen d.γB (1 : Qp).half ∗
    srvAlarmStoreAddr s ↦□ al ∗
    srvCfgFieldAddr s go!"DataDir" ↦□ dd ∗ backend.pathOwn (config.backendPathOf dd))

/-- **What `NewServer` hands the snapshot path** (see the file header): the bundle at a fresh
snapshot-taken counter, its authority at `0` (until J8a-6, 2026-11-01, the reader-slot stock);
(D22 J1b) the backend's own resources (`srvSnapRes`). -/
def srvSnapBoot (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ γt : GName, srvSnapRO s ci E γr γt ∗ monoNatAuthOwn γt 1 0 ∗ srvSnapRes s E)

/-- **The apply thread's snapshot resources at the applied index `ai`** (D22 J1b, 2026-10-31;
`notes/snapshot-sj-plan.md`, J1b; spatial): the persistent bundle at the snapshot-taken counter
`γt`, the counter's authority at most `ai` (`specSnap`'s `hnt`) and the backend's own resources
(`srvSnapRes`; until J8a-6, 2026-11-01, also the reader-slot stock for the installs'
`AddPeer`s). `run`'s loop invariant holds it (`applyRes`), at the current backend's environment
`E`; `applyAll` passes it through a batch. The transport's live state is `srvApRes`'s (J-T). -/
def srvSnapOwn (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (ai : w64) : IProp GF :=
  iprop(∃ (γt : GName) (nt : Nat), srvSnapRO s ci E γr γt ∗ ⌜nt ≤ uint.nat ai⌝ ∗
    monoNatAuthOwn γt 1 nt ∗ srvSnapRes s E)

/-- The resources hold at any larger applied index. -/
theorem srvSnapOwn_mono (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (ai ai' : w64)
    (h : uint.Z ai ≤ uint.Z ai') :
    srvSnapOwn (GF := GF) s ci E γr ai ⊢ srvSnapOwn s ci E γr ai' := by
  iintro H
  iunfold srvSnapOwn at H
  icases H with ⟨%γt, %nt, #Hro, %Hnt, Ha, Hres⟩
  iunfold srvSnapOwn
  iexists γt, nt
  iframe Hro Ha Hres
  ipureintro
  have : uint.nat ai ≤ uint.nat ai' := by word
  omega

/-- **`run`'s start from `NewServer`'s**: the boot resources give the apply thread's at any
applied index (the counter at `0`), and the persistent bundle. -/
theorem srvSnapOwn_of_boot (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (ai : w64) :
    srvSnapBoot (GF := GF) s ci E γr ⊢
      srvSnapOwn s ci E γr ai ∗ ∃ γt : GName, srvSnapRO s ci E γr γt := by
  iintro H
  iunfold srvSnapBoot at H
  icases H with ⟨%γt, #Hro, Ha, Hres⟩
  isplitl [Ha Hres]
  · iunfold srvSnapOwn
    iexists γt, 0
    iframe Hro Ha Hres
    ipureintro; exact Nat.zero_le _
  · iexists γt; iexact Hro

end defs

end EtcdGrove
end Perennial
