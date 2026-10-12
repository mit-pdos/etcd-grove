/-
The contracts of the components the apply package calls through interfaces or names-only
struct pointers (`server/v3/etcdserver/apply`): the trust boundary, each a persistent predicate
of triples (as the txn package's `isTxnLessor`). Lean-first (no Rocq counterpart); plan:
`notes/decisions.md`, "The server's apply".

**The hook's contract** (`csContract P f Pre Q Post`): the shape of every write to the backend
under its batch lock, the apply thread's protocol (`apply.Apply.spec`): the caller hands the
writer its `Pre`, the post-lock hook's triple `{P ∗ Pre} f() {Q}` and the update
`Q ={⊤}=∗ P ∗ Post` (the write itself); a writer that takes the lock (`P`), runs the hook,
writes and unlocks returns `Post`, one that does not write returns `Pre` (`Post ∨ Pre`). `P` is
the batch lock's invariant and `f` the hook, fixed per backend. The txn package's write path
gets the same shape through mvcc (unit A of the apply plan: `hookIs`, `store.Write`): the
definition is mvcc's (`InvStore.lean`), shared by both.

**The components** (each with the hook's `P f` where it writes the backend):
* `isAuthStore st P f` (`auth.AuthStore`): the permission checks (`Is*Permitted`) return some
  error and keep the caller's `AuthInfo`; `HasRole`, `IsAuthEnabled`, `Revision` return; every
  other method is a `csContract` and returns, for a response, `nil` or a fresh one whose
  `Header` can be set (`respHdrOk`).
* `isApplyLessor le γ P f` (`lease.Lessor`): the txn package's `isTxnLessor`, and `Grant`
  (`csContract`; a lease the lessor knows, `leaseIs`), `Revoke` (`csContract`; at the sole
  writer of `log`, it deletes keys through the store: the sole writer of `log` with deletions
  committed), `Checkpoint` (`csContract`), `Lookup` (nil or a lease, `leaseIs`: its `ID`, and its
  `TTL()` and `Keys()` return).
* `isAlarmStore st P f` (`*v3alarm.AlarmStore`): `Get` returns a slice, `Activate`/`Deactivate`
  are `csContract`s returning nil or an alarm member (`alarmMemberIs`).
* `isCluster c P f` (`*membership.RaftCluster`): `Version` (a pointer, maybe nil), `ID`;
  `SetVersion`, `UpdateAttributes`, `SetDowngradeInfo` are `csContract`s.
* `isRaftStatus rs`, `isSnapshotServer ss`, `isConsistentIndexer ci`: their methods return.
* `isApplyKV kv s γ`: the txn package's `isKV` and the store's `ReadView` (`KV.Rev()` is
  `store.Rev`, verified).
* `isQuota q` (`storage.Quota`): `Available` (some boolean) and `Cost` (some integer) on the three
  request types the appliers pass (any other type panics in `BackendQuota.Cost`).
The `wait.Wait`'s contract is `waitOk` (`Wait.lean`, shared with the server).

**Their errors** (2026-10-12, the merge of unit 2 with the `errors.Is` model): every error the
auth store's and the lessor's methods return is one `errors.Is` can take (`applyErrIs`: in an
error tree, whose errors of a pointer target's type hold pointers). An assumption of the
contracts, as the rest of them: true of etcd's `auth` errors (`errors.New` errors of
`auth/store.go`, `ErrPermissionDenied`, ...) and `lease` errors (`ErrLeaseNotFound`, ...,
`errors.New` too); what `dispatch`'s `errors.Is(ar.Err, mvcc.ErrCompacted)` and the server's
`errors.Is(ar.Err, ErrNoSpace)` need of the applier's result.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Wait
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The hook's contract -/

/-- The caller's resources are its own to give back: with nothing written, `Pre`. (The
contract is mvcc's `csContract`, `InvStore.lean`.) -/
theorem csContract_pre (P : IProp GF) (f : val) (Pre Q Post : IProp GF) :
    mvcc.csContract P f Pre Q Post ⊢ Pre := by
  unfold mvcc.csContract
  iintro ⟨HPre, -, -⟩
  iexact HPre

/-- **The contract of a write that happens only with `shouldApplyV3`** (`b`): the critical-section
contract if `b`, else only `Pre` (no backend write: an entry already in the backend, replayed).
The cluster's writers (`SetVersion`, `UpdateAttributes`, `SetDowngradeInfo`: `if shouldApplyV3 {
c.be.MustSave...ToBackend(...) }`) and, through them, the appliers' cluster methods and
`dispatch` take it (unit 2: `apply.Apply` without `v3` writes nothing). -/
def cPre (b : Bool) (P : IProp GF) (f : val) (Pre Q Post : IProp GF) : IProp GF :=
  if b then mvcc.csContract P f Pre Q Post else Pre

/-- What a writer under `cPre b` returns: `Post ∨ Pre` (`b`), `Pre` (not `b`). -/
def cPost (b : Bool) (Pre Post : IProp GF) : IProp GF :=
  if b then iprop(Post ∨ Pre) else Pre

theorem cPre_pre (b : Bool) (P : IProp GF) (f : val) (Pre Q Post : IProp GF) :
    cPre b P f Pre Q Post ⊢ Pre := by
  cases b
  · simp only [cPre, Bool.false_eq_true, ↓reduceIte]; iintro H; iexact H
  · simp only [cPre, ↓reduceIte]; exact csContract_pre P f Pre Q Post

theorem cPost_of_pre (b : Bool) (Pre Post : IProp GF) : Pre ⊢ cPost b Pre Post := by
  cases b
  · simp only [cPost, Bool.false_eq_true, ↓reduceIte]; iintro H; iexact H
  · simp only [cPost, ↓reduceIte]; iintro H; iright; iexact H

/-! ## Responses -/

/-- A response of type `T` returned by a component: `nil`, or a fresh one whose `Header` the
applier sets (`resp.Header = a.newHeader()`). -/
def respHdrOk (T : Type) (resp : Loc) : IProp GF :=
  iprop(⌜resp = null⌝ ∨ ∃ h : Loc, structFieldRef T go!"Header" resp ↦ h)

/-! ## The auth store -/

/-- An auth-store method taking a request `r` and returning `(resp, err)` with `resp` of type
`T`: a `csContract` (a write under the batch lock, or none). -/
def authReqContract (ai : GoInterfaceOk) (m : GoString) (T : Type) (P : IProp GF) (f : val) :
    IProp GF :=
  iprop(□ (∀ (r : Loc) (Pre Q Post : IProp GF),
    {{ mvcc.csContract P f Pre Q Post }} (App (Val #(methods ai.ty m ai.v)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗
        respHdrOk T resp ∗ applyErrIs err }}))

/-- A permission check `m(authInfo, key...)` of the auth store: some error; the caller's
`AuthInfo` and keys kept. -/
def permCheck2 (ai : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8)
      (dk : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k }}
      (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ applyErrIs err }}))

/-- A permission check `m(authInfo, key, rangeEnd)` of the auth store. -/
def permCheck3 (ai : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key re : GoSlice) (k e : List w8)
      (dk de : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e }}
      (App (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key)) (Val #re))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
        applyErrIs err }}))

/-- **The `auth.AuthStore` `st`** as the apply package uses it (trust boundary: `auth` is
names-only), whose writes run under the batch lock with invariant `P` and hook `f`. -/
def isAuthStore (st : GoInterface) (P : IProp GF) (f : val) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    permCheck2 ai go!"IsPutPermitted" ∗
    permCheck3 ai go!"IsRangePermitted" ∗
    permCheck3 ai go!"IsDeleteRangePermitted" ∗
    □ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac),
      {{ a ↦{dq} info }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #a))
      {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ applyErrIs err }}) ∗
    □ (∀ (u r : GoString),
      {{ True }} (App (App (Val #(methods ai.ty go!"HasRole" ai.v)) (Val #u)) (Val #r))
      {{ (b : Bool), RET #b; True }}) ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"IsAuthEnabled" ai.v)) (Val #()))
      {{ (b : Bool), RET #b; True }}) ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"Revision" ai.v)) (Val #()))
      {{ (x : w64), RET #x; True }}) ∗
    □ (∀ (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }} (App (Val #(methods ai.ty go!"AuthEnable" ai.v)) (Val #()))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ applyErrIs err }}) ∗
    □ (∀ (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }} (App (Val #(methods ai.ty go!"AuthDisable" ai.v)) (Val #()))
      {{ RET #(); Post ∨ Pre }}) ∗
    □ (∀ (ctx : GoInterface) (name pw : GoString) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }}
        (App (App (App (Val #(methods ai.ty go!"Authenticate" ai.v)) (Val #ctx)) (Val #name))
          (Val #pw))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗
          respHdrOk etcdserverpb.AuthenticateResponse resp ∗ applyErrIs err }}) ∗
    authReqContract ai go!"UserAdd" etcdserverpb.AuthUserAddResponse P f ∗
    authReqContract ai go!"UserDelete" etcdserverpb.AuthUserDeleteResponse P f ∗
    authReqContract ai go!"UserChangePassword" etcdserverpb.AuthUserChangePasswordResponse P f ∗
    authReqContract ai go!"UserGrantRole" etcdserverpb.AuthUserGrantRoleResponse P f ∗
    authReqContract ai go!"UserGet" etcdserverpb.AuthUserGetResponse P f ∗
    authReqContract ai go!"UserRevokeRole" etcdserverpb.AuthUserRevokeRoleResponse P f ∗
    authReqContract ai go!"RoleAdd" etcdserverpb.AuthRoleAddResponse P f ∗
    authReqContract ai go!"RoleGrantPermission" etcdserverpb.AuthRoleGrantPermissionResponse P f ∗
    authReqContract ai go!"RoleGet" etcdserverpb.AuthRoleGetResponse P f ∗
    authReqContract ai go!"RoleRevokePermission" etcdserverpb.AuthRoleRevokePermissionResponse P f ∗
    authReqContract ai go!"RoleDelete" etcdserverpb.AuthRoleDeleteResponse P f ∗
    authReqContract ai go!"UserList" etcdserverpb.AuthUserListResponse P f ∗
    authReqContract ai go!"RoleList" etcdserverpb.AuthRoleListResponse P f)

instance isAuthStore_persistent (st : GoInterface) (P : IProp GF) (f : val) :
    Persistent (isAuthStore st P f) := by
  unfold isAuthStore permCheck2 permCheck3 authReqContract; infer_instance

/-! ## The lessor -/

/-- The `*lease.Lease` `l` (not nil): its `ID`, and its `TTL()` and `Keys()` return (`Keys` a
fresh slice of the lease's keys). -/
def leaseIs (l : Loc) (id : w64) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ structFieldRef lease.Lease go!"ID" l ↦□ id ∗
    □ ({{ True }} (App (Val (l @!! go.GoType.PointerType lease.Lease.ty @!! go!"TTL")) (Val #()))
      {{ (t : w64), RET #t; True }}) ∗
    □ ({{ True }} (App (Val (l @!! go.GoType.PointerType lease.Lease.ty @!! go!"Keys")) (Val #()))
      {{ (sl : GoSlice), RET #sl; ∃ ks : List GoString, sl ↦* ks }}))

instance leaseIs_persistent (l : Loc) (id : w64) : Persistent (leaseIs (GF := GF) l id) := by
  unfold leaseIs; infer_instance

/-- **The `lease.Lessor` `le`** as the apply package uses it (trust boundary: `lease` is
names-only): the txn package's `isTxnLessor`, its writes under the batch lock (`P`, `f`); a
revocation deletes the lease's keys through the store `γ`'s writer, one revision, under the
same lock (`lessor.Revoke`: `le.rd()` is the store's `Write`), which at the sole writer is a
commit of deletions. -/
def isApplyLessor (le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) :
    IProp GF :=
  iprop(txn.isTxnLessor le γ.leases ∗ ∃ li : GoInterfaceOk, ⌜le = GoInterface.ok li⌝ ∗
    □ (∀ (id ttl : w64) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }}
        (App (App (Val #(methods li.ty go!"Grant" li.v)) (Val #id)) (Val #ttl))
      {{ (l : Loc) (err : GoInterface), RET (PairV #l #err); (Post ∨ Pre) ∗
          (⌜err ≠ GoInterface.nil⌝ ∨
            (⌜err = GoInterface.nil⌝ ∗ ∃ id' : w64, leaseIs l id' ∗ mvcc.leaseKnown γ.leases id')) ∗
          applyErrIs err }}) ∗
    □ (∀ (id : w64) (log : mvcc.Log) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ txn.soleWriter γ log }}
        (App (Val #(methods li.ty go!"Revoke" li.v)) (Val #id))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗
          (∃ pend : List mvcc.Change, ⌜∀ c ∈ pend, c.isDel = true⌝ ∗
            txn.soleWriter γ (mvcc.commitLog log pend)) ∗ applyErrIs err }}) ∗
    □ (∀ (id rem : w64) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }}
        (App (App (Val #(methods li.ty go!"Checkpoint" li.v)) (Val #id)) (Val #rem))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ applyErrIs err }}) ∗
    □ (∀ id : w64,
      {{ True }} (App (Val #(methods li.ty go!"Lookup" li.v)) (Val #id))
      {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ leaseIs l id }}))

instance isApplyLessor_persistent (le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF)
    (f : val) : Persistent (isApplyLessor le γ P f) := by
  unfold isApplyLessor; infer_instance

/-! ## The alarm store, the cluster, the raft status, the snapshot server -/

/-- The `*pb.AlarmMember` `m` (not nil): its `Alarm`, read-only. -/
def alarmMemberIs (m : Loc) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ a : w32, structFieldRef etcdserverpb.AlarmMember go!"Alarm" m ↦□ a)

instance alarmMemberIs_persistent (m : Loc) : Persistent (alarmMemberIs (GF := GF) m) := by
  unfold alarmMemberIs; infer_instance

/-- **The `*v3alarm.AlarmStore` `st`** (trust boundary: `v3alarm` is names-only): `Get` returns
a slice (its own: a loop over its map, under its mutex); `Activate` and `Deactivate` write the
alarm bucket under the batch lock (or not: an alarm already set, or not set). -/
def isAlarmStore (st : Loc) (P : IProp GF) (f : val) : IProp GF :=
  iprop(⌜st ≠ null⌝ ∗
    □ (∀ at' : w32,
      {{ True }}
        (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get"))
          (Val #at'))
      {{ (sl : GoSlice), RET #sl; True }}) ∗
    □ (∀ (id : w64) (at' : w32) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }}
        (App (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!!
          go!"Activate")) (Val #id)) (Val #at'))
      {{ (m : Loc), RET #m; (Post ∨ Pre) ∗ (⌜m = null⌝ ∨ alarmMemberIs m) }}) ∗
    □ (∀ (id : w64) (at' : w32) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post }}
        (App (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!!
          go!"Deactivate")) (Val #id)) (Val #at'))
      {{ (m : Loc), RET #m; (Post ∨ Pre) ∗ (⌜m = null⌝ ∨ alarmMemberIs m) }}))

instance isAlarmStore_persistent (st : Loc) (P : IProp GF) (f : val) :
    Persistent (isAlarmStore st P f) := by
  unfold isAlarmStore; infer_instance

/-- **The `*membership.RaftCluster` `c`** (trust boundary: `membership` is names-only):
`Version` (a `*semver.Version`, maybe nil) and `ID` return; `SetVersion` (with a version not
nil), `UpdateAttributes` and `SetDowngradeInfo` (which keeps the `DowngradeInfo` pointer) write
the cluster's bucket under the batch lock only with `shouldApplyV3` (`cPre b`: the
critical-section contract; without it, no write: `ApplyV2storeOnly`; unit 2). -/
def isCluster (c : Loc) (P : IProp GF) (f : val) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗
    □ ({{ True }}
        (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"Version")) (Val #()))
      {{ (v : Loc), RET #v; True }}) ∗
    □ ({{ True }}
        (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"ID")) (Val #()))
      {{ (id : w64), RET #id; True }}) ∗
    □ (∀ (v : Loc) (onSet : val) (b : Bool) (Pre Q Post : IProp GF),
      {{ cPre b P f Pre Q Post ∗ ⌜v ≠ null⌝ }}
        (App (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty
          @!! go!"SetVersion")) (Val #v)) (Val onSet)) (Val #b))
      {{ RET #(); cPost b Pre Post }}) ∗
    □ (∀ (id : w64) (attr : etcdserver.api.membership.Attributes) (b : Bool)
        (Pre Q Post : IProp GF),
      {{ cPre b P f Pre Q Post }}
        (App (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty
          @!! go!"UpdateAttributes")) (Val #id)) (Val #attr)) (Val #b))
      {{ RET #(); cPost b Pre Post }}) ∗
    □ (∀ (d : Loc) (di : etcdserver.version.DowngradeInfo) (b : Bool) (Pre Q Post : IProp GF),
      {{ cPre b P f Pre Q Post ∗ d ↦ di }}
        (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"SetDowngradeInfo")) (Val #d)) (Val #b))
      {{ RET #(); cPost b Pre Post }}))

instance isCluster_persistent (c : Loc) (P : IProp GF) (f : val) :
    Persistent (isCluster c P f) := by
  unfold isCluster; infer_instance

/-- **The `RaftStatusGetter` `rs`** (the server): `MemberID`, `Leader`, `Term` return. -/
def isRaftStatus (rs : GoInterface) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rs = GoInterface.ok ri⌝ ∗
    □ ({{ True }} (App (Val #(methods ri.ty go!"MemberID" ri.v)) (Val #()))
      {{ (x : w64), RET #x; True }}) ∗
    □ ({{ True }} (App (Val #(methods ri.ty go!"Leader" ri.v)) (Val #()))
      {{ (x : w64), RET #x; True }}) ∗
    □ ({{ True }} (App (Val #(methods ri.ty go!"Term" ri.v)) (Val #()))
      {{ (x : w64), RET #x; True }}))

instance isRaftStatus_persistent (rs : GoInterface) : Persistent (isRaftStatus (GF := GF) rs) := by
  unfold isRaftStatus; infer_instance

/-- **The `SnapshotServer` `ss`** (the server): `ForceSnapshot` returns (it signals the apply
loop; no backend write here). -/
def isSnapshotServer (ss : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜ss = GoInterface.ok si⌝ ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"ForceSnapshot" si.v)) (Val #()))
      {{ RET #(); True }}))

instance isSnapshotServer_persistent (ss : GoInterface) :
    Persistent (isSnapshotServer (GF := GF) ss) := by
  unfold isSnapshotServer; infer_instance

/-- **The `cindex.ConsistentIndexer` `ci`**: `ConsistentIndex` returns (the authenticate
request's token index). -/
def isConsistentIndexer (ci : GoInterface) : IProp GF :=
  iprop(∃ cii : GoInterfaceOk, ⌜ci = GoInterface.ok cii⌝ ∗
    □ ({{ True }} (App (Val #(methods cii.ty go!"ConsistentIndex" cii.v)) (Val #()))
      {{ (x : w64), RET #x; True }}))

instance isConsistentIndexer_persistent (ci : GoInterface) :
    Persistent (isConsistentIndexer (GF := GF) ci) := by
  unfold isConsistentIndexer; infer_instance

/-! ## The KV -/

/-- **The `mvcc.KV` `kv`** as the backend applier uses it: the txn package's `isKV` (the store
`*store` at `s`), and its `ReadView` field, the `readView` `NewStore` installs (`KV.Rev()`,
`newHeader`, is its `Rev`: `store.Rev`'s spec). -/
def isApplyKV (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) : IProp GF :=
  iprop(txn.isKV kv s γ ∗ ∃ rv : Loc,
    structFieldRef storage.mvcc.store go!"ReadView" s ↦□
      (interface.mkOk (go.GoType.PointerType storage.mvcc.readView.ty) #rv : GoInterface) ∗
    mvcc.isReadView rv s γ)

instance isApplyKV_persistent (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) :
    Persistent (isApplyKV (GF := GF) kv s γ) := by
  unfold isApplyKV; infer_instance

/-! ## The quota -/

/-- The request types the appliers pass a quota (`BackendQuota.Cost` panics on any other). -/
def quotaReqTy (t : go.GoType) : Prop :=
  t = go.GoType.PointerType etcdserverpb.PutRequest.ty ∨
  t = go.GoType.PointerType etcdserverpb.TxnRequest.ty ∨
  t = go.GoType.PointerType etcdserverpb.LeaseGrantRequest.ty

/-- **The `storage.Quota` `q`** (trust boundary: `storage` is names-only): `Available` (whether
the backend has room) and `Cost` return, on the three request types. -/
def isQuota (q : GoInterface) : IProp GF :=
  iprop(∃ qi : GoInterfaceOk, ⌜q = GoInterface.ok qi⌝ ∗
    □ (∀ (t : go.GoType) (p : Loc), ⌜quotaReqTy t⌝ -∗
      {{ True }} (App (Val #(methods qi.ty go!"Available" qi.v)) (Val #(interface.mkOk t #p)))
      {{ (b : Bool), RET #b; True }}) ∗
    □ (∀ (t : go.GoType) (p : Loc), ⌜quotaReqTy t⌝ -∗
      {{ True }} (App (Val #(methods qi.ty go!"Cost" qi.v)) (Val #(interface.mkOk t #p)))
      {{ (c : w64), RET #c; True }}))

instance isQuota_persistent (q : GoInterface) : Persistent (isQuota (GF := GF) q) := by
  unfold isQuota; infer_instance

end defs

end apply
end EtcdGrove
end Perennial
