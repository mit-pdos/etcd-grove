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
* `isAuthStore st P f RD` (`auth.AuthStore`): the permission checks (`Is*Permitted`, with the
  caller's reader resource `RD` and the key's length bound) return some error and keep the
  caller's `AuthInfo`; `HasRole`, `IsAuthEnabled` (with `RD`), `Revision` return; every
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Wait
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Writer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.auth.Model

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
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

/-! ## The backend's write budget -/

/-! ## The auth store -/

/-- **Whether the auth store's admin requests are admitted** in the mode `M` (the auth plan's E2i,
2026-10-26): in the mode `off`; in the modes `on γa` and `any` not yet. `isAuthStore`'s admin
clauses (`HasRole`, `AuthEnable`, `AuthDisable`, `Authenticate`, the user and role requests) take
it: in the mode `on` they need the admin side's authority `auth.authOwn` and the step premises
`auth.stepOk` (`apply/AuthSteps.lean`), which the request's admission will carry once the server's
workload admits an auth request (`rqOk` admits none: `notes/decisions.md`, "E2i of the auth plan").
In the mode `on` the clauses are then vacuous, and the real store meets them
(`isAuthStoreAdmin_on`). -/
def adminAdmitted (M : auth.AuthMode) : Prop := M.isOn = false

theorem adminAdmitted_on (γa : auth.AuthNames) : ¬ adminAdmitted (.on γa) := by
  simp [adminAdmitted, auth.AuthMode.isOn]

/-- An auth-store method taking a request `r` and returning `(resp, err)` with `resp` of type
`T`: a `csContract` (a write under the batch lock, or none), with the write right `RW` of the
rest buckets it writes (D22, 2026-10-23: the backend over every bucket), given back; admitted in
the mode `M` only (`adminAdmitted`, E2i). -/
def authReqContract (ai : GoInterfaceOk) (m : GoString) (T : Type) (γ : mvcc.StoreNames)
    (P : IProp GF) (f : val) (RW : IProp GF) (M : auth.AuthMode) : IProp GF :=
  iprop(□ (∀ (r : Loc) (Pre Q Post : IProp GF),
    {{ ⌜adminAdmitted M⌝ ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ RW }} (App (Val #(methods ai.ty m ai.v)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ mvcc.storeRT γ ∗
        respHdrOk T resp ∗ applyErrIs err ∗ RW }}))

/-- An auth-store method adding a user or a role (`m` `UserAdd` or `RoleAdd`) from a request `r`
whose name (`Is r n`, read-only) is within bbolt's key bound: as `authReqContract`. The name is
the new record's bbolt key, and a longer one makes the backend's put fatal
(`issues/etcd-auth-useradd-long-name-fatal.md`; unit N4, D14g, 2026-10-17: until then the
clause took any request, false of the Go code). The workload clause bounds the names (`rqOk`). -/
def authReqContractN (ai : GoInterfaceOk) (m : GoString) (T : Type) (γ : mvcc.StoreNames)
    (P : IProp GF) (f : val) (RW : IProp GF) (Is : Loc → GoString → IProp GF) (M : auth.AuthMode) :
    IProp GF :=
  iprop(□ (∀ (r : Loc) (n : GoString) (Pre Q Post : IProp GF),
    {{ ⌜adminAdmitted M⌝ ∗ Is r n ∗ ⌜n.length ≤ backend.maxKeySize⌝ ∗ mvcc.csContract P f Pre Q Post ∗
        mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ RW }} (App (Val #(methods ai.ty m ai.v)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ mvcc.storeRT γ ∗
        respHdrOk T resp ∗ applyErrIs err ∗ RW }}))

/-- A permission check `m(authInfo, key)` of the auth store (`IsPutPermitted`: a write of the
point `key`), with the caller's reader resource `RD` (held and given back) and the key shorter
than `2 ^ 63 - 1`: an error the gRPC layer can take, with its verdict in the mode `M`
(`auth.permVerdict`: in the mode `off` the check passes; `notes/auth-plan.md`, A0); the caller's
`AuthInfo` and keys kept. -/
def permCheck2 (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) (M : auth.AuthMode) :
    IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8)
      (dk : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ applyErrIs err ∗
        ⌜M.isOn = false → err = GoInterface.nil⌝ ∗ auth.permVerdict M info k [] .write err }}))

/-- A permission check `m(authInfo, key, rangeEnd)` of the auth store (as `permCheck2`;
`IsRangePermitted` with `op = .read`, `IsDeleteRangePermitted` with `op = .write`). -/
def permCheck3 (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) (M : auth.AuthMode)
    (op : auth.PermType) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key re : GoSlice) (k e : List w8)
      (dk de : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key)) (Val #re))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ RD ∗
        applyErrIs err ∗ ⌜M.isOn = false → err = GoInterface.nil⌝ ∗
        auth.permVerdict M info k e op err }}))

/-- **The `auth.AuthStore` `st`** as the apply package uses it, whose writes run under the batch
lock with invariant `P` and hook `f`, and whose request side takes the caller's reader resource
`RD` (2026-10-14, unit A2: the real store's methods read-lock its `RWMutex`es and the backend's
read transaction, a reader slot each; `auth.authRd st R` of the real store). The permission checks,
`IsAdminPermitted`, `IsAuthEnabled` and `Revision` are the real store's (`isAuthStore_of_authInv`,
`AuthDerive.lean`); `HasRole` and the admin requests (`AuthEnable` ...) are its contract
(`isAuthStoreAdmin`, the premise), admitted in the mode `off` only (`adminAdmitted`; the auth plan's
E2i, 2026-10-26: in the mode `on` vacuous, the real store's `isAuthStoreAdmin_on`).

**Its mode `M`** (`auth.AuthMode`; 2026-10-14, unit T1, as a boolean; 2026-10-23, the auth plan's
A0, with the verdicts): in the mode `off` the store is disabled and stays so (Go's `isOpPermitted`
and `IsAdminPermitted` return `nil` when `!as.IsAuthEnabled()`): the permission checks and
`IsAdminPermitted` return `nil`, `IsAuthEnabled` `false`, and `AuthEnable` is not called (its
precondition `⌜M.isOn = true⌝`); in the mode `on γa` each check's answer is a verdict over the
store's recorded states (`auth.permVerdict`, `auth.adminVerdict`, `auth.enabledVerdict`,
`auth.revisionVerdict`: `auth/Model.lean`); in the mode `any` nothing is promised of the answers,
which is what the real store's proofs give until the auth plan's track S (`AuthDerive.lean`).

**Its writes' right `RW`** (D22, 2026-10-23: the backend over every bucket): the writing methods
take and give back the right to write the auth buckets (the real store's, `∃ r, backend.rbOwn γB
r`: its writes change the backend's tracked buckets); the server's environment has none (`AEnv.RW
= False`), its workload admitting no auth request.

**`IsAdminPermitted(nil)`** (the last clause; the auth plan's S3, 2026-10-23): the API layer's
admin guards pass `AuthInfoFromCtx`'s answer, `nil` for a request without a token, and the real
method answers it (`ErrUserEmpty` with auth enabled: `adminVerdict M none err`). A clause of its
own, after the others, so that the apply layer's callers, which pass a field's address, keep
the non-`nil` clause's shape (the real store's spec, `auth.authStore.IsAdminPermitted.spec`,
covers both in one, over `auth.authInfoAt`). -/
def isAuthStore (st : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RD : IProp GF)
    (M : auth.AuthMode) (RW : IProp GF) :
    IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    permCheck2 ai go!"IsPutPermitted" RD M ∗
    permCheck3 ai go!"IsRangePermitted" RD M .read ∗
    permCheck3 ai go!"IsDeleteRangePermitted" RD M .write ∗
    □ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac),
      {{ a ↦{dq} info ∗ RD }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #a))
      {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ RD ∗ applyErrIs err ∗
          ⌜M.isOn = false → err = GoInterface.nil⌝ ∗ auth.adminVerdict M (some info) err }}) ∗
    □ (∀ (u r : GoString),
      {{ ⌜adminAdmitted M⌝ }} (App (App (Val #(methods ai.ty go!"HasRole" ai.v)) (Val #u)) (Val #r))
      {{ (b : Bool), RET #b; True }}) ∗
    □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAuthEnabled" ai.v)) (Val #()))
      {{ (b : Bool), RET #b; RD ∗ auth.enabledVerdict M b }}) ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"Revision" ai.v)) (Val #()))
      {{ (x : w64), RET #x; auth.revisionVerdict M x }}) ∗
    □ (∀ (Pre Q Post : IProp GF),
      {{ ⌜adminAdmitted M⌝ ∗ ⌜M.isOn = true⌝ ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.storeWT γ ∗
          mvcc.storeRT γ ∗ RW }}
        (App (Val #(methods ai.ty go!"AuthEnable" ai.v)) (Val #()))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ mvcc.storeRT γ ∗ applyErrIs err ∗ RW }}) ∗
    □ (∀ (Pre Q Post : IProp GF),
      {{ ⌜adminAdmitted M⌝ ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ RW }}
        (App (Val #(methods ai.ty go!"AuthDisable" ai.v)) (Val #()))
      {{ RET #(); (Post ∨ Pre) ∗ mvcc.storeRT γ ∗ RW }}) ∗
    □ (∀ (ctx : GoInterface) (name pw : GoString) (Pre Q Post : IProp GF),
      {{ ⌜adminAdmitted M⌝ ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ RW }}
        (App (App (App (Val #(methods ai.ty go!"Authenticate" ai.v)) (Val #ctx)) (Val #name))
          (Val #pw))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ mvcc.storeRT γ ∗
          respHdrOk etcdserverpb.AuthenticateResponse resp ∗ applyErrIs err ∗ RW }}) ∗
    authReqContractN ai go!"UserAdd" etcdserverpb.AuthUserAddResponse γ P f RW auth.userAddReqIs M ∗
    authReqContract ai go!"UserDelete" etcdserverpb.AuthUserDeleteResponse γ P f RW M ∗
    authReqContract ai go!"UserChangePassword" etcdserverpb.AuthUserChangePasswordResponse γ P f RW M ∗
    authReqContract ai go!"UserGrantRole" etcdserverpb.AuthUserGrantRoleResponse γ P f RW M ∗
    authReqContract ai go!"UserGet" etcdserverpb.AuthUserGetResponse γ P f RW M ∗
    authReqContract ai go!"UserRevokeRole" etcdserverpb.AuthUserRevokeRoleResponse γ P f RW M ∗
    authReqContractN ai go!"RoleAdd" etcdserverpb.AuthRoleAddResponse γ P f RW authRoleAddIs M ∗
    authReqContract ai go!"RoleGrantPermission" etcdserverpb.AuthRoleGrantPermissionResponse γ P f RW M ∗
    authReqContract ai go!"RoleGet" etcdserverpb.AuthRoleGetResponse γ P f RW M ∗
    authReqContract ai go!"RoleRevokePermission" etcdserverpb.AuthRoleRevokePermissionResponse γ P f RW M ∗
    authReqContract ai go!"RoleDelete" etcdserverpb.AuthRoleDeleteResponse γ P f RW M ∗
    authReqContract ai go!"UserList" etcdserverpb.AuthUserListResponse γ P f RW M ∗
    authReqContract ai go!"RoleList" etcdserverpb.AuthRoleListResponse γ P f RW M ∗
    □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #(null : Loc)))
      {{ (err : GoInterface), RET #err; RD ∗ applyErrIs err ∗
          ⌜M.isOn = false → err = GoInterface.nil⌝ ∗ auth.adminVerdict M none err }}))

instance isAuthStore_persistent (st : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RD : IProp GF) (M : auth.AuthMode) (RW : IProp GF) : Persistent (isAuthStore st γ P f RD M RW) := by
  unfold isAuthStore permCheck2 permCheck3 authReqContract authReqContractN; infer_instance

/-! ## The lessor -/

/-- The `*lease.Lease` `l` (not nil): its `ID`, and its `TTL()` and `Keys()` return (`Keys` a
fresh slice of the lease's keys, each shorter than `2 ^ 63 - 1`: 2026-10-14, unit A2, the auth
store's `IsPutPermitted` of each needs it; true of every string in memory). -/
def leaseIs (l : Loc) (id : w64) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ structFieldRef lease.Lease go!"ID" l ↦□ id ∗
    □ ({{ True }} (App (Val (l @!! go.GoType.PointerType lease.Lease.ty @!! go!"TTL")) (Val #()))
      {{ (t : w64), RET #t; True }}) ∗
    □ ({{ True }} (App (Val (l @!! go.GoType.PointerType lease.Lease.ty @!! go!"Keys")) (Val #()))
      {{ (sl : GoSlice), RET #sl; ∃ ks : List GoString, sl ↦* ks ∗
          ⌜∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1⌝ }}))

instance leaseIs_persistent (l : Loc) (id : w64) : Persistent (leaseIs (GF := GF) l id) := by
  unfold leaseIs; infer_instance

/-- The `*lease.Lease` `l` (not nil) a grant returns: its `ID`, and its `TTL()` returns (2026-10-13,
unit 9: `Grant` is proved, `lease.lessor.Grant.spec`; its lease's `Keys()` read-locks the lease's
`mu`, a reader slot the grant does not give, and the apply package does not call it on a
granted lease). -/
def leaseTTLIs (l : Loc) (id : w64) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ structFieldRef lease.Lease go!"ID" l ↦□ id ∗
    □ ({{ True }} (App (Val (l @!! go.GoType.PointerType lease.Lease.ty @!! go!"TTL")) (Val #()))
      {{ (t : w64), RET #t; True }}))

instance leaseTTLIs_persistent (l : Loc) (id : w64) : Persistent (leaseTTLIs (GF := GF) l id) := by
  unfold leaseTTLIs; infer_instance

/-- **The `lease.Lessor` `le`** as the apply package uses it (trust boundary: `lease` is
names-only): the txn package's `isTxnLessor`, its writes under the batch lock (`P`, `f`); a
revocation deletes the lease's keys through the store `γ`'s writer, one revision, under the
same lock (`lessor.Revoke`: `le.rd()` is the store's `Write`, which spends a write token,
`mvcc.storeWT γ`; 2026-10-13, unit 6), which at the sole writer is a commit of deletions.
The live set (2026-10-13, unit 8 of the backend: the lessor's `GetLease`, `Attach`, `Detach`,
`Lookup` and `SetRangeDeleter` are proved, `isTxnLessor` derived): `Grant` and `Revoke` take the
lease owner's half (`lease.leaseOwn γ.leases L`); a grant only adds to the live set (a granted
lease in it), a revocation (at the KV's writer, `txn.kvWriter s γ`: unit N4, its range deleter writes through
the KV over the store `s`) removes the lease and, deleting its keys (`l.Keys()`, the lease's item
set, which the store's puts and deletes keep through `Attach`/`Detach`), keeps every lease of the
state live (`txn.leasesKnown`). Still assumed (the lessor's other methods are not proved).
2026-10-13, unit 9: `Grant` and `Checkpoint` are proved (`lease.lessor.Grant.spec`,
`lease.lessor.Checkpoint.spec`) and their clauses derived of the real lessor
(`lease.isApplyLessor_of_lessorInv`, with this contract's `Revoke` and `Lookup` clauses as its
premises); a granted lease is `leaseTTLIs` (no `Keys()`). (D22, 2026-10-23) `Grant` and
`Checkpoint` take the write right `RW` of the lease bucket, spent with the write-back token (the
lessor's backend contract `lease.lessorBackend` takes both per write); the server's `AEnv.RW` is
the backend's tracked buckets' half, which its apply thread does not lend (no lease request is
admitted). -/
def isApplyLessor (le : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RW : IProp GF) : IProp GF :=
  iprop(txn.isTxnLessor le γ.leases ∗ ∃ li : GoInterfaceOk, ⌜le = GoInterface.ok li⌝ ∗
    □ (∀ (id ttl : w64) (L : List w64) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ lease.leaseOwn γ.leases L ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗
          lease.leaseGranted γ.leases id ∗ RW }}
        (App (App (Val #(methods li.ty go!"Grant" li.v)) (Val #id)) (Val #ttl))
      {{ (l : Loc) (err : GoInterface), RET (PairV #l #err); (Post ∨ Pre) ∗ mvcc.storeRT γ ∗
          (∃ L' : List w64, lease.leaseOwn γ.leases L' ∗ ⌜∀ x ∈ L, x ∈ L'⌝ ∗
            (⌜err ≠ GoInterface.nil⌝ ∨
              (⌜err = GoInterface.nil⌝ ∗ ∃ id' : w64, leaseTTLIs l id' ∗ ⌜id' ∈ L'⌝))) ∗
          applyErrIs err }}) ∗
    -- `Revoke` (D14h, 2026-10-17): vacuous (`⌜False⌝`): the workload has no lease request
    -- (`rqOk`), and `lessor.Revoke` is not specified (unit T3: it needs the lessor's invariant to
    -- record the store's range deleter)
    □ (∀ (id : w64) (log : mvcc.Log) (L : List w64) (Pre Q Post : IProp GF),
      {{ ⌜False⌝ ∗ mvcc.csContract P f Pre Q Post ∗ txn.kvWriter s γ log ∗ mvcc.storeWT γ ∗
          lease.leaseOwn γ.leases L ∗ txn.leasesKnown L (mvcc.stateAfter log) ∗
          (□ ∀ pend : List mvcc.Change, ⌜∀ c ∈ pend, c.isDel = true⌝ -∗
            mvcc.certOkNext γ log pend) }}
        (App (Val #(methods li.ty go!"Revoke" li.v)) (Val #id))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗
          (∃ (pend : List mvcc.Change) (L' : List w64), ⌜∀ c ∈ pend, c.isDel = true⌝ ∗
            txn.kvWriter s γ (mvcc.commitLog log pend) ∗ lease.leaseOwn γ.leases L' ∗
            txn.leasesKnown L' (mvcc.stateAfter (mvcc.commitLog log pend))) ∗
          applyErrIs err }}) ∗
    □ (∀ (id rem : w64) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ RW }}
        (App (App (Val #(methods li.ty go!"Checkpoint" li.v)) (Val #id)) (Val #rem))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ mvcc.storeRT γ ∗ applyErrIs err }}) ∗
    □ (∀ id : w64,
      {{ True }} (App (Val #(methods li.ty go!"Lookup" li.v)) (Val #id))
      {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ leaseIs l id }}))

instance isApplyLessor_persistent (le : GoInterface) (s : Loc) (γ : mvcc.StoreNames)
    (P : IProp GF) (f : val) (RW : IProp GF) : Persistent (isApplyLessor le s γ P f RW) := by
  unfold isApplyLessor; infer_instance

/-- The lessor's contract over some store (what the permission checks take: they call only
`Lookup`; unit N4: `isApplyLessor`'s `Revoke` clause names the KV's store `s`). -/
def isApplyLessorAny (le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RW : IProp GF) : IProp GF :=
  iprop(∃ s : Loc, isApplyLessor le s γ P f RW)

instance isApplyLessorAny_persistent (le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF)
    (f : val) (RW : IProp GF) : Persistent (isApplyLessorAny le γ P f RW) := by
  unfold isApplyLessorAny; infer_instance

theorem isApplyLessorAny_of (le : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF)
    (f : val) (RW : IProp GF) : isApplyLessor (GF := GF) le s γ P f RW ⊢ isApplyLessorAny le γ P f RW := by
  unfold isApplyLessorAny; iintro H; iexists s; iexact H

/-! ## The alarm store, the cluster, the raft status, the snapshot server -/

/-- The `*pb.AlarmMember` `m` (not nil): its `Alarm`, read-only. -/
def alarmMemberIs (m : Loc) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ a : w32, structFieldRef etcdserverpb.AlarmMember go!"Alarm" m ↦□ a)

instance alarmMemberIs_persistent (m : Loc) : Persistent (alarmMemberIs (GF := GF) m) := by
  unfold alarmMemberIs; infer_instance

/-- **The `*v3alarm.AlarmStore` `st`** (trust boundary: `v3alarm` is names-only): `Get` returns
a slice (its own: a loop over its map, under its mutex); `Activate` and `Deactivate` write the
alarm bucket under the batch lock (or not: an alarm already set, or not set). `Activate` takes an alarm type other than `NONE` (`0`): the
member `{0, NONE}` encodes to an empty bbolt key, fatal (`issues/etcd-alarm-activate-none-zero-fatal.md`;
unit N4, 2026-10-17); its one caller, `applierV3backend.Alarm`, skips `NONE`. (D22,
2026-10-23) The writes take and give back the alarm bucket's write right `RW` (as the auth
store's). -/
def isAlarmStore (st : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RW : IProp GF) :
    IProp GF :=
  iprop(⌜st ≠ null⌝ ∗
    □ (∀ at' : w32,
      {{ True }}
        (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get"))
          (Val #at'))
      {{ (sl : GoSlice), RET #sl; True }}) ∗
    □ (∀ (id : w64) (at' : w32) (Pre Q Post : IProp GF),
      {{ ⌜at' ≠ W32 0⌝ ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ RW }}
        (App (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!!
          go!"Activate")) (Val #id)) (Val #at'))
      {{ (m : Loc), RET #m; (Post ∨ Pre) ∗ mvcc.storeRT γ ∗ (⌜m = null⌝ ∨ alarmMemberIs m) ∗ RW }}) ∗
    □ (∀ (id : w64) (at' : w32) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ RW }}
        (App (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!!
          go!"Deactivate")) (Val #id)) (Val #at'))
      {{ (m : Loc), RET #m; (Post ∨ Pre) ∗ mvcc.storeRT γ ∗ (⌜m = null⌝ ∨ alarmMemberIs m) ∗ RW }}))

instance isAlarmStore_persistent (st : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RW : IProp GF) : Persistent (isAlarmStore st γ P f RW) := by
  unfold isAlarmStore; infer_instance

/-- **The alarm store's `Get`** (persistent; `isAlarmStore`'s first clause, which names no
environment: the uber-applier's construction calls it before the environment's hook exists;
unit N4, 2026-10-17). -/
def alarmGetOk (st : Loc) : IProp GF :=
  iprop(□ (∀ at' : w32,
      {{ True }}
        (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get"))
          (Val #at'))
      {{ (sl : GoSlice), RET #sl; True }}))

instance alarmGetOk_persistent (st : Loc) : Persistent (alarmGetOk (GF := GF) st) := by
  unfold alarmGetOk; infer_instance

/-- **The alarm store's `Get` under a resource `T`**, returning no alarm if `z` (D14i,
2026-10-17: a fresh alarm store's, `alarmFresh`, during the uber-applier's construction;
`alarmGetOk` is `T = True`, `z = false`). -/
def alarmGetIs (st : Loc) (T : IProp GF) (z : Bool) : IProp GF :=
  iprop(□ (∀ at' : w32,
      {{ T }}
        (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get"))
          (Val #at'))
      {{ (sl : GoSlice), RET #sl; T ∗ ⌜z = true → sl.len = W64 0⌝ }}))

instance alarmGetIs_persistent (st : Loc) (T : IProp GF) (z : Bool) :
    Persistent (alarmGetIs (GF := GF) st T z) := by
  unfold alarmGetIs; infer_instance

theorem alarmGetIs_of_ok (st : Loc) : alarmGetOk (GF := GF) st ⊢ alarmGetIs st iprop(True) false := by
  iintro #H
  iunfold alarmGetOk at H
  iunfold alarmGetIs
  iintro !> %at' %Φ !> - HΦ
  iapply H $$ [] [HΦ]
  · itrivial
  inext
  iintro %sl -
  iapply HΦ
  isplitr
  · itrivial
  ipureintro; intro h; cases h

theorem alarmGetOk_of (st : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RW : IProp GF) :
    isAlarmStore (GF := GF) st γ P f RW ⊢ alarmGetOk st := by
  iintro #H
  iunfold isAlarmStore at H
  icases H with ⟨-, #HG, -⟩
  iunfold alarmGetOk
  iexact HG

/-- **The `*membership.RaftCluster` `c`** (trust boundary: `membership` is names-only):
`Version` (a `*semver.Version`, maybe nil) and `ID` return; `SetVersion` (with a version not
nil), `UpdateAttributes` and `SetDowngradeInfo` (which keeps the `DowngradeInfo` pointer) write
the cluster's bucket under the batch lock only with `shouldApplyV3` (`cPre b`: the
critical-section contract; without it, no write: `ApplyV2storeOnly`; unit 2). (D22, 2026-10-23:
the backend over every bucket) `SetVersion` and `UpdateAttributes` state their effect on the rest
buckets and the in-memory members through the environment's resource `RO` (`RestModel.lean`):
`SetVersion` of the version `MustParse(s)` (`semverIs`) saves `semverNorm s` with `b`
(`restSetVersion`); `UpdateAttributes` replaces the in-memory member's attributes and, with `b`,
saves that member (`restUpdateAttrs`: exception 7, the in-memory member); `SetDowngradeInfo`, which
the workload does not reach, takes the write right `RW`. -/
def isCluster (c : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RO : RestM → IProp GF)
    (RW : IProp GF) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗
    □ ({{ True }}
        (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"Version")) (Val #()))
      {{ (v : Loc), RET #v; True }}) ∗
    □ ({{ True }}
        (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"ID")) (Val #()))
      {{ (id : w64), RET #id; True }}) ∗
    □ (∀ (v : Loc) (s : GoString) (onSet : val) (b : Bool) (Pre Q Post : IProp GF) (r : RestM),
      {{ cPre b P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ ⌜v ≠ null⌝ ∗ semverIs v s ∗
          RO r }}
        (App (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty
          @!! go!"SetVersion")) (Val #v)) (Val onSet)) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ mvcc.storeRT γ ∗ RO (restSetVersion b s r) }}) ∗
    □ (∀ (id : w64) (attr : etcdserver.api.membership.Attributes) (cus : List GoString) (b : Bool)
        (Pre Q Post : IProp GF) (r : RestM),
      {{ cPre b P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗
          attr.ClientURLs' ↦*□ cus ∗ RO r }}
        (App (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty
          @!! go!"UpdateAttributes")) (Val #id)) (Val #attr)) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ mvcc.storeRT γ ∗
          RO (restUpdateAttrs b ⟨id, attr.Name', cus⟩ r) }}) ∗
    □ (∀ (d : Loc) (di : etcdserver.version.DowngradeInfo) (b : Bool) (Pre Q Post : IProp GF),
      {{ cPre b P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ d ↦ di ∗ RW }}
        (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"SetDowngradeInfo")) (Val #d)) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ mvcc.storeRT γ ∗ RW }}))

instance isCluster_persistent (c : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RO : RestM → IProp GF) (RW : IProp GF) : Persistent (isCluster c γ P f RO RW) := by
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
loop; no backend write here), under the apply thread's right `FS` (D14i, 2026-10-17: the server's
`ForceSnapshot` writes `s.forceDiskSnapshot`, a field of the apply thread's). -/
def isSnapshotServer (ss : GoInterface) (FS : IProp GF) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜ss = GoInterface.ok si⌝ ∗
    □ ({{ FS }} (App (Val #(methods si.ty go!"ForceSnapshot" si.v)) (Val #()))
      {{ RET #(); FS }}))

instance isSnapshotServer_persistent (ss : GoInterface) (FS : IProp GF) :
    Persistent (isSnapshotServer (GF := GF) ss FS) := by
  unfold isSnapshotServer; infer_instance

/-- **The `cindex.ConsistentIndexer` `ci`**: `ConsistentIndex` returns (the authenticate
request's token index), under any resource `C` of the kind `K` (D14i, 2026-10-17: the server's
consistent index reads its backend field with the owner's share and may load the index, so its
caller lends the apply thread's resources, given back). -/
def isConsistentIndexer (ci : GoInterface) (K : IProp GF → Prop) : IProp GF :=
  iprop(∃ cii : GoInterfaceOk, ⌜ci = GoInterface.ok cii⌝ ∗
    □ (∀ C : IProp GF, ⌜K C⌝ -∗
      {{ C }} (App (Val #(methods cii.ty go!"ConsistentIndex" cii.v)) (Val #()))
      {{ (x : w64), RET #x; C }}))

instance isConsistentIndexer_persistent (ci : GoInterface) (K : IProp GF → Prop) :
    Persistent (isConsistentIndexer (GF := GF) ci K) := by
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

/-- **The backend stays under its quota** (opaque, a named workload premise, D19a's first kind;
audit phase B3, D19h, 2026-10-18, adopted by the user): every `Available` of the run's quotas
answers true, i.e. the backend's size plus a request's cost stays below the configured quota
(`BackendQuota.Available`, `storage/quota.go`: 2 GiB by default). True of putget (one small key);
false of a workload that fills the quota, which the closed theorem then does not cover: the
NOSPACE path (the quota's `ErrNoSpace`, the NOSPACE alarm, the capped applier) stays outside the
model. A premise of `storage.NewBackendQuota`'s axiom, so of the constructions above it
(`newQuotaApplierV3` ... `NewServer.spec`; v3rpc's `newBackendQuota` ... `v3rpc.Server`). The
model of the alarm instead (D19h's option (A)) is the later route for a theorem covering a full
disk. Every backend of the run: after a snapshot's install a quota may still read the replaced,
closed backend, whose `Size()` is its last value (D22 S-k, `storage.NewBackendQuota.spec`). -/
opaque backendUnderQuota : Prop

/-- **The `storage.Quota` `q`** (trust boundary: `storage` is names-only): `Available` and `Cost`
return, on the three request types. **`Available` returns `true`** (2026-10-14, unit T1): under
the named premise `backendUnderQuota` (audit phase B3, 2026-10-18; until then an unstated
construction premise), which `storage.NewBackendQuota` takes; so no applier sets `ErrNoSpace` and
`quotaAlarmer.check` never proposes the NOSPACE `Alarm`. -/
def isQuota (q : GoInterface) : IProp GF :=
  iprop(∃ qi : GoInterfaceOk, ⌜q = GoInterface.ok qi⌝ ∗
    □ (∀ (t : go.GoType) (p : Loc), ⌜quotaReqTy t⌝ -∗
      {{ True }} (App (Val #(methods qi.ty go!"Available" qi.v)) (Val #(interface.mkOk t #p)))
      {{ (b : Bool), RET #b; ⌜b = true⌝ }}) ∗
    □ (∀ (t : go.GoType) (p : Loc), ⌜quotaReqTy t⌝ -∗
      {{ True }} (App (Val #(methods qi.ty go!"Cost" qi.v)) (Val #(interface.mkOk t #p)))
      {{ (c : w64), RET #c; True }}))

instance isQuota_persistent (q : GoInterface) : Persistent (isQuota (GF := GF) q) := by
  unfold isQuota; infer_instance

end defs

end apply
end EtcdGrove
end Perennial
