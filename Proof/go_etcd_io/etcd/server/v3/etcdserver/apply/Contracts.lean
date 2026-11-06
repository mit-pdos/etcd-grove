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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestLease
public import Proof.go_etcd_io.etcd.server.v3.lease.RangeDeleter
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Wait
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreCore
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
open mvcc.api (MvccName mvccLeases MvccState MvccReachable isMvcc mvccBackend hookIs
  mvccDeleter)
open srvApi (csContractA auBegin auEnd)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The hook's contract -/

/-- The caller's resources are its own to give back: with nothing written, `Pre`. (The
contract is mvcc's `csContract`, `InvStore.lean`.) -/
theorem csContract_pre (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) :
    csContractA P f Pre Q Post ⊢ Pre := by
  unfold csContractA
  iintro ⟨HPre, -, -⟩
  iexact HPre

/-- **The contract of a write that happens only with `shouldApplyV3`** (`b`): the critical-section
contract if `b`, else only `Pre` (no backend write: an entry already in the backend, replayed).
The cluster's writers (`SetVersion`, `UpdateAttributes`, `SetDowngradeInfo`: `if shouldApplyV3 {
c.be.MustSave...ToBackend(...) }`) and, through them, the appliers' cluster methods and
`dispatch` take it (unit 2: `apply.Apply` without `v3` writes nothing). -/
def cPre (b : Bool) (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) : IProp GF :=
  if b then csContractA P f Pre Q Post else Pre

/-- What a writer under `cPre b` returns: `Post ∨ Pre` (`b`), `Pre` (not `b`). -/
def cPost (b : Bool) (Pre Post : IProp GF) : IProp GF :=
  if b then iprop(Post ∨ Pre) else Pre

theorem cPre_pre (b : Bool) (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) :
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

/-- **A write-back token of the backend `B`** (strict M1, 2026-11-05, decided by the coordinator:
in place of mvcc's `storeWT γ`, which was exactly the token of `γ`'s backend): what a component's
write under the batch lock spends at its `Unlock`. -/
def bkWT (B : mvcc.KBReal) : IProp GF := backend.wbTok B.γB

/-- **A reader token of the backend `B`** (in place of mvcc's `storeRT γ`, the same of `γ`'s
backend): a component's read, lent and given back. -/
def bkRT (B : mvcc.KBReal) : IProp GF :=
  iprop(backend.rdTok B.γB B.P B.be ∗ backend.bOpen B.γB backend.rdOpen)

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
def authReqContract (ai : GoInterfaceOk) (m : GoString) (T : Type) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RW : IProp GF) (M : auth.AuthMode) : IProp GF :=
  iprop(□ (∀ (r : Loc) (B : mvcc.KBReal) (Pre Q Post : IProp GF),
    {{ ⌜adminAdmitted M⌝ ∗ csContractA (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗ RW }} (App (Val #(methods ai.ty m ai.v)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗
        respHdrOk T resp ∗ applyErrIs err ∗ RW }}))

/-- An auth-store method adding a user or a role (`m` `UserAdd` or `RoleAdd`) from a request `r`
whose name (`Is r n`, read-only) is within bbolt's key bound: as `authReqContract`. The name is
the new record's bbolt key, and a longer one makes the backend's put fatal
(`issues/etcd-auth-useradd-long-name-fatal.md`; unit N4, D14g, 2026-10-17: until then the
clause took any request, false of the Go code). The workload clause bounds the names (`rqOk`). -/
def authReqContractN (ai : GoInterfaceOk) (m : GoString) (T : Type) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RW : IProp GF) (Is : Loc → GoString → IProp GF) (M : auth.AuthMode) :
    IProp GF :=
  iprop(□ (∀ (r : Loc) (n : GoString) (B : mvcc.KBReal) (Pre Q Post : IProp GF),
    {{ ⌜adminAdmitted M⌝ ∗ Is r n ∗ ⌜n.length ≤ backend.maxKeySize⌝ ∗ csContractA (Pk B) f Pre Q Post ∗
        bkWT B ∗ bkRT B ∗ BT B ∗ RW }} (App (Val #(methods ai.ty m ai.v)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗
        respHdrOk T resp ∗ applyErrIs err ∗ RW }}))

/-- A permission check `m(authInfo, key)` of the auth store (`IsPutPermitted`: a write of the
point `key`), with the caller's reader resource `RD` (held and given back) and the key shorter
than `2 ^ 63 - 1`: an error the gRPC layer can take and one of the auth package's
(`authApplyErrIs`; the auth plan's E3i, 2026-10-27), with its verdict in the mode `M`
(`auth.permVerdict`: in the mode `off` the check passes; `notes/auth-plan.md`, A0); the caller's
`AuthInfo` and keys kept. -/
def permCheck2 (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) (M : auth.AuthMode) :
    IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8)
      (dk : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ authApplyErrIs err ∗
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
        authApplyErrIs err ∗ ⌜M.isOn = false → err = GoInterface.nil⌝ ∗
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
def isAuthStore (st : GoInterface) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RD : IProp GF)
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
    □ (∀ (B : mvcc.KBReal) (Pre Q Post : IProp GF),
      {{ ⌜adminAdmitted M⌝ ∗ ⌜M.isOn = true⌝ ∗ csContractA (Pk B) f Pre Q Post ∗ bkWT B ∗
          bkRT B ∗ BT B ∗ RW }}
        (App (Val #(methods ai.ty go!"AuthEnable" ai.v)) (Val #()))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗ applyErrIs err ∗ RW }}) ∗
    □ (∀ (B : mvcc.KBReal) (Pre Q Post : IProp GF),
      {{ ⌜adminAdmitted M⌝ ∗ csContractA (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗ RW }}
        (App (Val #(methods ai.ty go!"AuthDisable" ai.v)) (Val #()))
      {{ RET #(); (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗ RW }}) ∗
    □ (∀ (ctx : GoInterface) (name pw : GoString) (B : mvcc.KBReal) (Pre Q Post : IProp GF),
      {{ ⌜adminAdmitted M⌝ ∗ csContractA (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗ RW }}
        (App (App (App (Val #(methods ai.ty go!"Authenticate" ai.v)) (Val #ctx)) (Val #name))
          (Val #pw))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗
          respHdrOk etcdserverpb.AuthenticateResponse resp ∗ applyErrIs err ∗ RW }}) ∗
    authReqContractN ai go!"UserAdd" etcdserverpb.AuthUserAddResponse Pk f BT RW auth.userAddReqIs M ∗
    authReqContract ai go!"UserDelete" etcdserverpb.AuthUserDeleteResponse Pk f BT RW M ∗
    authReqContract ai go!"UserChangePassword" etcdserverpb.AuthUserChangePasswordResponse Pk f BT RW M ∗
    authReqContract ai go!"UserGrantRole" etcdserverpb.AuthUserGrantRoleResponse Pk f BT RW M ∗
    authReqContract ai go!"UserGet" etcdserverpb.AuthUserGetResponse Pk f BT RW M ∗
    authReqContract ai go!"UserRevokeRole" etcdserverpb.AuthUserRevokeRoleResponse Pk f BT RW M ∗
    authReqContractN ai go!"RoleAdd" etcdserverpb.AuthRoleAddResponse Pk f BT RW authRoleAddIs M ∗
    authReqContract ai go!"RoleGrantPermission" etcdserverpb.AuthRoleGrantPermissionResponse Pk f BT RW M ∗
    authReqContract ai go!"RoleGet" etcdserverpb.AuthRoleGetResponse Pk f BT RW M ∗
    authReqContract ai go!"RoleRevokePermission" etcdserverpb.AuthRoleRevokePermissionResponse Pk f BT RW M ∗
    authReqContract ai go!"RoleDelete" etcdserverpb.AuthRoleDeleteResponse Pk f BT RW M ∗
    authReqContract ai go!"UserList" etcdserverpb.AuthUserListResponse Pk f BT RW M ∗
    authReqContract ai go!"RoleList" etcdserverpb.AuthRoleListResponse Pk f BT RW M ∗
    □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #(null : Loc)))
      {{ (err : GoInterface), RET #err; RD ∗ applyErrIs err ∗
          ⌜M.isOn = false → err = GoInterface.nil⌝ ∗ auth.adminVerdict M none err }}))

instance isAuthStore_persistent (st : GoInterface) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF)
    (RD : IProp GF) (M : auth.AuthMode) (RW : IProp GF) : Persistent (isAuthStore st Pk f BT RD M RW) := by
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

/-- **The log after revoking `id`** (the lease-revoke plan, 2026-10-31): the lease's keys deleted
at one revision (`mvcc.leaseDels`), none if it has none. -/
abbrev revokeLog (log : mvcc.Log) (id : w64) : mvcc.Log :=
  mvcc.commitLog log (mvcc.leaseDels (mvcc.stateAfter log) id)

/-- **`isApplyLessor`'s `Revoke` clause** (D3; strict M1, 2026-11-05: `lessor.Revoke.spec`'s shape
over mvcc's API) at the store `γ`, the batch lock of the backend `B` (`Pk B`, `f`), the backend's
tie `BT` and the rest resource `RO`: by the lease owner at the live set `L`, the range deleter held
(`mvccDeleter`), a share of the store's backend, the thread's token, the begin state `σ₀`
(reachable, nothing pending) and, for a live lease only (decided by the coordinator, 2026-11-06:
`if decide (id ∈ L) then … else True`, as `lessor.Revoke.spec`), one nested update, the deleter's
begin whose payload is the end of exactly the lease's deletions (`auBegin γ σ₀ (auEnd γ σ₀
(leaseDels …) Y)`):
* `id` not live: an error (`ErrLeaseNotFound`), nothing changed, `Pre` back;
* `id` live: no error, `Y`, `Post`, the live set without `id`, its record deleted from the `lease`
  bucket (`restRevoke`). -/
def revokeClause (le : GoInterfaceOk) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc)
    (BT : mvcc.KBReal → IProp GF) (RO : RestM → IProp GF) : IProp GF :=
  iprop(□ (∀ (id : w64) (σ₀ : MvccState) (L : List w64) (rs : RestM) (q : Qp) (B : mvcc.KBReal)
      (Pre Q Post Y : IProp GF),
    {{ threadTok ∗ (∃ rd : GoFunc, lease.rdOwn (mvccLeases γ) rd ∗ mvccDeleter rd γ) ∗
        mvccBackend γ q B (Pk B) ∗ hookIs B f ∗ BT B ∗ csContractA (Pk B) f Pre Q Post ∗
        ⌜σ₀.pending = none ∧ (mvcc.stateAfter σ₀.log).length ≤ 2 ^ 62 ∧ MvccReachable σ₀ ∧
          σ₀.log.length + 3 ≤ 2 ^ 63⌝ ∗
        (if decide (id ∈ L) then
          auBegin γ σ₀ (auEnd γ σ₀ (mvcc.leaseDels (mvcc.stateAfter σ₀.log) id) Y)
        else iprop(True)) ∗
        lease.leaseOwn (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter σ₀.log)) ∗
        lease.leaseRevokers (mvccLeases γ) L ∗ txn.leasesKnown L (mvcc.stateAfter σ₀.log) ∗ RO rs }}
      (App (Val #(methods le.ty go!"Revoke" le.v)) (Val #id))
    {{ (err : GoInterface), RET #err; threadTok ∗
        (∃ rd : GoFunc, lease.rdOwn (mvccLeases γ) rd ∗ mvccDeleter rd γ) ∗
        mvccBackend γ q B (Pk B) ∗ BT B ∗ applyErrIs err ∗
        ((⌜id ∉ L ∧ mvcc.leaseDels (mvcc.stateAfter σ₀.log) id = []⌝ ∗
            (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□
              GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝) ∗ Pre ∗
            lease.leaseOwn (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter σ₀.log)) ∗
            lease.leaseRevokers (mvccLeases γ) L ∗ txn.leasesKnown L (mvcc.stateAfter σ₀.log) ∗
            RO rs) ∨
         (⌜id ∈ L ∧ err = GoInterface.nil⌝ ∗ Y ∗ Post ∗
            lease.leaseOwn (mvccLeases γ) (L.filter (· != id)) (mvcc.leaseItemsOf (mvcc.stateAfter
              (revokeLog σ₀.log id))) ∗
            lease.leaseRevokers (mvccLeases γ) (L.filter (· != id)) ∗
            txn.leasesKnown (L.filter (· != id)) (mvcc.stateAfter (revokeLog σ₀.log id)) ∗
            RO (restRevoke id rs))) }}))

/-- **The `lease.Lessor` `le`** as the apply package uses it (trust boundary: `lease` is
names-only; strict M1, 2026-11-05: over mvcc's API, the store `γ`, the batch lock `Pk B` of the
current backend `B` (tied by `BT`), its hook `f`, the backend's write-back and reader tokens
`bkWT B`/`bkRT B` in place of mvcc's `storeWT`/`storeRT`, decided by the coordinator): the txn
package's `isTxnLessor`; `Grant` (a lease the lessor knows, `leaseTTLIs`), `Revoke`
(`revokeClause`), `Checkpoint` under the batch lock, `Lookup` (nil or a lease, `leaseIs`). `Grant`
and `Checkpoint` take the write right `RW` of the lease bucket and give it back (the coordinator's
decision, 2026-11-06: the lessor's backend lends `le.b` from the resource its writes give back). -/
def isApplyLessor (le : GoInterface) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc)
    (BT : mvcc.KBReal → IProp GF) (RO : RestM → IProp GF) (RW : IProp GF) : IProp GF :=
  iprop(txn.isTxnLessor le (mvccLeases γ) ∗ ∃ li : GoInterfaceOk, ⌜le = GoInterface.ok li⌝ ∗
    □ (∀ (id ttl : w64) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
        (B : mvcc.KBReal) (Pre Q Post : IProp GF),
      {{ csContractA (Pk B) f Pre Q Post ∗ lease.leaseOwn (mvccLeases γ) L I ∗
          lease.leaseRevokers (mvccLeases γ) L ∗ bkWT B ∗ bkRT B ∗ BT B ∗
          lease.leaseGranted (mvccLeases γ) id ∗ RW }}
        (App (App (Val #(methods li.ty go!"Grant" li.v)) (Val #id)) (Val #ttl))
      {{ (l : Loc) (err : GoInterface), RET (PairV #l #err); (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗ RW ∗
          (∃ L' : List w64, lease.leaseOwn (mvccLeases γ) L' I ∗ lease.leaseRevokers (mvccLeases γ) L' ∗
            ⌜∀ x ∈ L, x ∈ L'⌝ ∗
            (⌜err ≠ GoInterface.nil⌝ ∨
              (⌜err = GoInterface.nil⌝ ∗ ∃ id' : w64, leaseTTLIs l id' ∗ ⌜id' ∈ L'⌝))) ∗
          applyErrIs err }}) ∗
    revokeClause li γ Pk f BT RO ∗
    □ (∀ (id rem : w64) (B : mvcc.KBReal) (Pre Q Post : IProp GF),
      {{ csContractA (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗ RW }}
        (App (App (Val #(methods li.ty go!"Checkpoint" li.v)) (Val #id)) (Val #rem))
      {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗ RW ∗ applyErrIs err }}) ∗
    □ (∀ id : w64,
      {{ True }} (App (Val #(methods li.ty go!"Lookup" li.v)) (Val #id))
      {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ leaseIs l id }}))

instance revokeClause_persistent (le : GoInterfaceOk) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF)
    (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RO : RestM → IProp GF) :
    Persistent (revokeClause le γ Pk f BT RO) := by
  unfold revokeClause; infer_instance

instance isApplyLessor_persistent (le : GoInterface) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF)
    (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RO : RestM → IProp GF) (RW : IProp GF) :
    Persistent (isApplyLessor le γ Pk f BT RO RW) := by
  unfold isApplyLessor; infer_instance

/-- The lessor's contract at some rest resource (what the permission checks take: they call only
`Lookup`). -/
def isApplyLessorAny (le : GoInterface) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc)
    (BT : mvcc.KBReal → IProp GF) (RW : IProp GF) : IProp GF :=
  iprop(∃ RO : RestM → IProp GF, isApplyLessor le γ Pk f BT RO RW)

instance isApplyLessorAny_persistent (le : GoInterface) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF)
    (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RW : IProp GF) :
    Persistent (isApplyLessorAny le γ Pk f BT RW) := by
  unfold isApplyLessorAny; infer_instance

theorem isApplyLessorAny_of (le : GoInterface) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc)
    (BT : mvcc.KBReal → IProp GF) (RO : RestM → IProp GF) (RW : IProp GF) :
    isApplyLessor (GF := GF) le γ Pk f BT RO RW ⊢ isApplyLessorAny le γ Pk f BT RW := by
  unfold isApplyLessorAny; iintro H; iexists RO; iexact H

/-- **The lease owner's view, when the checking thread has it** (the lease-keys plan): `some (L,
I)` on the apply thread, which lends the transaction walk (`checkTxnPermission`) its owner's
resource (`lease.lessorUser`: `L` the live leases, `I` the item map); `none` on the server's read
path (`EtcdServer.Txn`'s `CheckTxnAuth`), which holds none and walks only read-only transactions
(every operation a get: no put, so no lease to look up; the walk's specs take that premise with
`none`). -/
abbrev LeaseView := Option (List w64 × GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)

/-- The owner's resource of the view (`lease.lessorUser`), nothing without one. -/
def lessorView (γl : GName) : LeaseView → IProp GF
  | none => iprop(True)
  | some (L, I) => lease.lessorUser γl L I

theorem lessorView_none (γl : GName) : lessorView (GF := GF) γl none = iprop(True) := rfl
theorem lessorView_some (γl : GName) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) :
    lessorView (GF := GF) γl (some (L, I)) = lease.lessorUser γl L I := rfl
/-! ## The alarm store, the cluster, the raft status, the snapshot server -/

/-- The `*pb.AlarmMember` `m` (not nil): its `Alarm`, read-only. -/
def alarmMemberIs (m : Loc) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ a : w32, structFieldRef etcdserverpb.AlarmMember go!"Alarm" m ↦□ a)

instance alarmMemberIs_persistent (m : Loc) : Persistent (alarmMemberIs (GF := GF) m) := by
  unfold alarmMemberIs; infer_instance

/-- **The `*v3alarm.AlarmStore` `st`** (trust boundary: `v3alarm` is names-only): `Get` returns
a slice (its own: a loop over its map, under its mutex); `Activate` and `Deactivate` write the
alarm bucket under the batch lock (or not: an alarm already set, or not set). `Activate` takes an alarm type other than `NONE` (`0`): the
member `{0, NONE}` encodes to an empty bbolt key, fatal (`nonissues/etcd-alarm-activate-none-zero-fatal.md`;
unit N4, 2026-10-17); its one caller, `applierV3backend.Alarm`, skips `NONE`. (D22,
2026-10-23) The writes take and give back the alarm bucket's write right `RW` (as the auth
store's). -/
def isAlarmStore (st : Loc) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RW : IProp GF) :
    IProp GF :=
  iprop(⌜st ≠ null⌝ ∗
    □ (∀ at' : w32,
      {{ True }}
        (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get"))
          (Val #at'))
      {{ (sl : GoSlice), RET #sl; True }}) ∗
    □ (∀ (id : w64) (at' : w32) (B : mvcc.KBReal) (Pre Q Post : IProp GF),
      {{ ⌜at' ≠ W32 0⌝ ∗ csContractA (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗ RW }}
        (App (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!!
          go!"Activate")) (Val #id)) (Val #at'))
      {{ (m : Loc), RET #m; (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗ (⌜m = null⌝ ∨ alarmMemberIs m) ∗ RW }}) ∗
    □ (∀ (id : w64) (at' : w32) (B : mvcc.KBReal) (Pre Q Post : IProp GF),
      {{ csContractA (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗ RW }}
        (App (App (Val (st @!! go.GoType.PointerType etcdserver.api.v3alarm.AlarmStore.ty @!!
          go!"Deactivate")) (Val #id)) (Val #at'))
      {{ (m : Loc), RET #m; (Post ∨ Pre) ∗ bkRT B ∗ BT B ∗ (⌜m = null⌝ ∨ alarmMemberIs m) ∗ RW }}))

instance isAlarmStore_persistent (st : Loc) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF)
    (RW : IProp GF) : Persistent (isAlarmStore st Pk f BT RW) := by
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
2026-10-17: a fresh alarm store's, during the uber-applier's construction, since 2026-11-01 the
user's half at no alarm, `alarmEmpty`, `AlarmGet.lean`;
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

theorem alarmGetOk_of (st : Loc) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RW : IProp GF) :
    isAlarmStore (GF := GF) st Pk f BT RW ⊢ alarmGetOk st := by
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
the workload does not reach, takes the write right `RW`. (2026-11-02, the cluster-rows stage:
`SetVersion`'s callback is `api.UpdateCapability`, the one Go passes, until then any value, which
Go calls (`cluster.go:623`), with `membership`'s and `api`'s package initialization (it writes
`ClusterVersionMetrics` and `api`'s capability globals; as `RaftCluster.Recover`'s axiom); its
version is not above the server's (`semverAtMostServer s`: `MustDetectDowngrade` panics above it,
before the `shouldApplyV3` test, `cluster.go:609-611`). `UpdateAttributes`' id is a member of `r.mem`
(an id neither a member nor removed panics, `cluster.go:479-486`; a removed id only warns, but the
server removes no member, its configuration changes being `AddNode`s of the boot configuration,
so the removed case is not claimed). The rest buckets present and the members' client URLs
read-only are in `RO`'s meaning (`srvRestOwn`, `memberAt`); for `SetDowngradeInfo`, the buckets
present in `RW`'s (`srvRestRW`). Claimed, and false, as before this stage: a saved value above
bbolt's `MaxValueSize` (a member's attributes, or a version string with a huge prerelease tag,
which sorts below the bound) is fatal in `unsafePut` (`batch_tx.go:183-188`); no caller makes one
(the monitor proposes `Major.Minor.0`, the attributes come from the configuration;
`issues/etcd-backend-put-value-too-large-fatal.md`).) -/
def isCluster (c : Loc) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF) (RO : RestM → IProp GF)
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
    □ (∀ (v : Loc) (s : GoString) (b : Bool) (B : mvcc.KBReal) (Pre Q Post : IProp GF) (r : RestM),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api ∗
          cPre b (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗ ⌜v ≠ null⌝ ∗ semverIs v s ∗
          ⌜semverAtMostServer s⌝ ∗ RO r }}
        (App (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty
          @!! go!"SetVersion")) (Val #v))
          (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.UpdateCapability))) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ bkRT B ∗ BT B ∗ RO (restSetVersion b s r) }}) ∗
    □ (∀ (id : w64) (attr : etcdserver.api.membership.Attributes) (cus : List GoString) (b : Bool)
        (B : mvcc.KBReal) (Pre Q Post : IProp GF) (r : RestM),
      {{ cPre b (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗
          attr.ClientURLs' ↦*□ cus ∗ ⌜(r.mem.lookup id).isSome = true⌝ ∗ RO r }}
        (App (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty
          @!! go!"UpdateAttributes")) (Val #id)) (Val #attr)) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ bkRT B ∗ BT B ∗
          RO (restUpdateAttrs b ⟨id, attr.Name', cus⟩ r) }}) ∗
    □ (∀ (d : Loc) (di : etcdserver.version.DowngradeInfo) (b : Bool) (B : mvcc.KBReal) (Pre Q Post : IProp GF),
      {{ cPre b (Pk B) f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ BT B ∗ d ↦ di ∗ RW }}
        (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"SetDowngradeInfo")) (Val #d)) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ bkRT B ∗ BT B ∗ RW }}))

instance isCluster_persistent (c : Loc) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF)
    (RO : RestM → IProp GF) (RW : IProp GF) : Persistent (isCluster c Pk f BT RO RW) := by
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

/-- **The `cindex.ConsistentIndexer` `ci`**: `ConsistentIndex` returns `x` (the authenticate
request's token index), under any resource `C` with `K C x` (D14i, 2026-10-17: the server's
consistent index reads its backend field with the owner's share and may load the index, so its
caller lends the apply thread's resources, given back; C1's A2, 2026-10-28: the value it returns,
which until then the contract left free). -/
def isConsistentIndexer (ci : GoInterface) (K : IProp GF → w64 → Prop) : IProp GF :=
  iprop(∃ cii : GoInterfaceOk, ⌜ci = GoInterface.ok cii⌝ ∗
    □ (∀ (C : IProp GF) (x : w64), ⌜K C x⌝ -∗
      {{ C }} (App (Val #(methods cii.ty go!"ConsistentIndex" cii.v)) (Val #()))
      {{ RET #x; C }}))

instance isConsistentIndexer_persistent (ci : GoInterface) (K : IProp GF → w64 → Prop) :
    Persistent (isConsistentIndexer (GF := GF) ci K) := by
  unfold isConsistentIndexer; infer_instance

/-! ## The KV -/

/-- **The `mvcc.KV` `kv`** as the backend applier uses it (strict M1, 2026-11-05): a store handle
of mvcc's API (`isMvcc`, under `□`: persistent by `persistent.law`; its methods' contracts by `shapes.law`; the chain's environment ties it to
`E.kv`, `backendOptsOk`). -/
def isApplyKV (kv : GoInterface) (γ : MvccName) : IProp GF := iprop(□ isMvcc kv γ)

instance isApplyKV_persistent (kv : GoInterface) (γ : MvccName) :
    Persistent (isApplyKV (GF := GF) kv γ) := by
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
