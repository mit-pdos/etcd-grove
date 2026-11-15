/-
# etcd's apply layer (`server/etcdserver/apply`, batch 3a): the vocabulary

What applying one committed `InternalRaftRequest` does (`apply.Apply`, the uber-applier, its chain
`corrupt? → capped? → auth → quota → backend`, `apply.go`, `uber_applier.go`, `auth.go`,
`quota.go`, `capped.go`, `corrupt.go`, `backend.go`), stated over W0's model (`EtcdModel.State`,
`Step`, `EnvStep`). Namespace `Apply`.

## The model of one apply, in words

**The decoded request** (`Irr`): the request id, the header (`Hdr`: the proposer's id, the user name
and the auth revision the request path stamped), and what it asks (`IrrOp`): one of W0's client
requests (`.req rq`, for the kinds that go through raft: `reqIsIrr`), a user added or a password
changed **with the stored hash** (`.userAdd`, `.userChangePassword`: the request path hashes the
password before proposing; the apply never sees it), a token assignment (`.authenticate`: the
password was checked before proposing), an alarm action (`.alarm`), a lease checkpoint, a cluster
version, a member's attributes (`.memberAttrSet`: `publishV3`), the downgrade info, or the test-only
`DowngradeVersionTest`. `irrDecodes bs ir` (provisional, 3h's): the bytes `bs` of a normal entry
decode (protobuf) to a message carrying `ir`.

**The apply's step** (`irrStep mc σ ir v3 σ' res`, transparent): what the member configured `mc`
does to the model state `σ` when it applies `ir` (`v3`: `shouldApplyV3`, false for the replay below
the consistent index), in Go's order:

1. the auth layer's administrator check (`needAdminPermission`, `IsAdminPermitted`: no revision
   check), before anything else, in both modes: a refusal with `AuthState.adminErr`;
2. the membership requests (cluster version, member attributes, downgrade info, the test request),
   in both modes: a member's attributes published (`EnvStep.publish` of W0, or nothing for a removed
   member), the rest invisible to the model;
3. without `v3`: nothing (the result is `nil`);
4. an alarm action (the uber-applier's `Alarm`, which every layer passes down): `GET` answers the
   alarms (`V3alarm.getOf`), `ACTIVATE` raises (`EnvStep.alarm`, a no-op if raised), `DEACTIVATE`
   clears;
5. the rest through the chain the raised alarms select (`chainOf σ`: `CORRUPT` adds the corrupt
   applier, `NOSPACE` the capped one): the corrupt applier refuses the KV and lease writes and reads
   (`.corrupt`), the capped one the puts, the transactions with a put and the grants (`.noSpace`),
   the auth applier checks the permissions **at the header's auth revision** (`checkErr`: auth on and
   revision `0` is `ErrUserEmpty`, **a revision older than the store's is `ErrAuthOldRevision`**, a
   missing user or an uncovered range `ErrPermissionDenied`; a lease's keys skipped for an
   administrator), the quota applier passes (its refusal is the result's, below), and the backend
   applier does the operation (`opStep`).

`applyStep mc σ e σ' res` (2d's name and signature): a normal entry `e` applied with `v3`: an empty
entry (a new leader's) changes nothing; otherwise its decoded request's `irrStep`. **A function**
(`applyStep_fun`): the state machine of every member moves alike, and the answer the proposer's apply
computes is the one the cluster fixes at the commit.

`opStep mc σ op σ' res` (opaque, a function: `opStep_fun`): **what the backend applier does** with a
request that passed the gates: mvcc's operation (3b's `txn` over 3e), the lessor's (3c), the auth
store's (3d). Its meaning is fixed by its laws: it is the request's own step of W0's model, never
one of `Step`'s refusals (`opStep_step`: `ownStep`, for an admitted request: the gRPC layer's
validation passed, `reqAdmitted`), it changes nothing for a token
assignment (`opStep_authenticate`), a hashed user change is W0's with the hash in the password's
place (`opStep_userAdd`, `opStep_userChangePassword`), a member's lease TTLs only change the TTLs
(`opStep_ttl`). It is opaque because Go's answer is a function W0 leaves relational (the order of a
sort's ties, `sort.Sort`; the token): its realization is the backend's deterministic computation over
its callees' models (3b, 3c, 3d).

**What the member's result carries** (`resMatch`, here; the result predicate in `ApiResult.lean`): the
step's answer, except (a) an alarm list in the alarm store's map order (a permutation), (b) a
transaction applied with `SkipRangeExecution` (no one waits: its ranges' answers empty, `skipRanges`),
(c) **the quota applier's `ErrNoSpace` after a put, a write transaction or a grant that it applied**
(`quota.go`: the write takes effect, the backend over its quota answers `ErrNoSpace`; the backend's
size is outside the model, so this is the one answer that is not a function of the state;
`nonissues/etcd-apply-quota-nospace-after-write.md`).

**Member configuration** (`MemberCfg`): the only member-specific input of the answer is the lessor's
minimum TTL (a grant's TTL is raised to it: `lessor.Grant`). Members configured differently compute
states that differ only in the leases' TTLs (`ttlEq`, `irrStep_ttl`): the cluster's history is
the proposer's, the other members' state machines are at a TTL-variant of it
(`nonissues/etcd-lease-ttl-differs-across-members.md`). **Settled**: `applyStep` takes the member's
configuration; 2d's `histAt` records the proposer's; a member's `smAt` is at its own TTL-variant
(the decision for the user, in `notes/specs-only/batch-3a.md`, is whether to instead require every
member configured alike).

## Resources

* `isUber ua mc γ γc R` (persistent): `ua` is an uber-applier (`NewUberApplier`'s) of a member
  configured `mc`, its replies' tokens registered in W0's cluster `γ` (`tokenUser`), its membership
  view named `γc` (2e's `Membership.clusterSt`), its calls lent `R` by the apply thread (2d's choice:
  what the backend's post-lock hook, `ConsistentIndex()` and `SnapshotServer.ForceSnapshot()` need).
  Its `Apply` method's triple is `isUber_apply` (`ApiResult.lean`), the bundle the interface call of
  `apply.Apply` uses.
* `smAt ua σ` (exclusive): **the member's state machine behind `ua` is at `σ`**: mvcc's store at
  `σ.kv`, the lessor's live leases `σ.leases` (and their attached keys, the store's), the auth store
  at `σ.auth`, the alarm store at `σ.alarms` with the chain it selects (`chainOf`), the backend's
  member buckets at `σ.members`. Held by the apply thread (2d).
* `memberUpd γc op Q` (transparent): for a member's attributes, the caller's atomic update of the
  membership's view (2e's `clusterSt γc`, which the server's invariant holds), whose precondition is
  that the member is known (`RaftCluster.UpdateAttributes` panics otherwise); `Q` for any other
  request. Fired in both modes (the in-memory view moves at the replay too).
* Internal (the package's own specs): `beAt b mc γ γc R` (the backend applier at `b`, persistent),
  `stAt b σ` (its stores at `σ`: `smAt`'s content), `applierAt v ls b aa` (the applier `v` is the
  layers `ls` over backend `b`, its auth layer `aa`), `aiAt aa ai` (the auth layer's `authInfo` field,
  owned while its mutex is held), `wrapperAt r ir sk`, `irrMsgAt p ir`, `reqMsgAt p dq op`
  (provisional, 3h's), `replyAt op res resp err` (a method's reply, `ApiResult.lean` relates it to
  2c's `applyResult`).

## Intended realization

`isUber ua mc γ γc R`: `ua = *uberApplier p`, its read-only `lg`, `alarmStore`,
`warningApplyDuration`, `applyV3base` fields, `applyV3base` the base chain (`applierAt _ [.auth,
.quota, .backend] b aa`), and `beAt b mc γ γc R`: the options' handles (mvcc's KV, the lessor with
minimum TTL `mc.minLeaseTTL`, the auth store with its token provider registering in `γ`, the alarm
store, the `RaftCluster` with view `γc`, the backend for the quota, the raft status getter's methods,
the snapshot server's and the consistent indexer's methods under `R`). `smAt ua σ`: `p.applyV3 ↦
v` with `applierAt v (chainLayers σ) b aa` and `stAt b σ`, which is the callees' exclusive states:
3e's store at `σ.kv`, 3c's lessor at `σ.leases` with the attachment of `σ.kv.store`'s lease fields,
3d's auth state `σ.auth`, 2e's `alarmSt γa σ.alarms` (the request path's concurrent `Alarms()` reads
are 2e's/2d's protocol: requested), 2e's `beView c st` with `st.members` a permutation of
`σ.members`; `granted`, `leaseHist` ghost. `aiAt aa u rev`: `aa.authInfo ↦ (u, rev)`; the mutex's
invariant is `aa.authInfo ↦ ("", 0)` (every path of `authApplierV3.Apply` resets the field before
unlocking, `auth.go:54-55,60-61`), so a header-less request (`auth.go:46`: the field kept) runs
with `("", 0)`, which is `aiAt aa ir.user ir.revW` (verify-round A9 F5).

## Laws

`isUber_persistent`, `smAt_excl`, `smAt_timeless`; the model: `irrDecodes_fun`, `opStep_fun`,
`opStep_total`, `opStep_step`, `opStep_authenticate`, `opStep_userAdd`, `opStep_userChangePassword`,
`opStep_ttl`, and the consequences 2c and 2d use, stated as laws (provable from the definitions and
the laws above): `irrStep_fun`, `applyStep_fun`, `applyStep_total`, `irrStep_step` (a client request's
apply is a `Step` of W0 by its principal), `irrStep_env` (an alarm or a publication is an `EnvStep`
or nothing), `irrStep_quiet` (a checkpoint, a token, a version, a downgrade: nothing),
`irrStep_noV3`, `irrStep_oldRev` (a stale auth revision changes nothing), `irrStep_ttl`; round 1:
`reachable`, `irrStep_alarm`, `irrStep_read`, `applyStep_reach`, `applyStep_ttl_same`,
`opStep_noOldRev`, `opStep_read`, `uberOpts` with `smAt_optsSt`, `smAt_alarms`.

## Verify round (2026-11-09, `notes/specs-only/verify/repair-apply-txn.md`)

* `txnAdmitted` includes 3b's `Txn.txnSafe` (A9 F1: a delete then an ignore-put of the same key
  panics in `txn.put`; the server gets it from 2a's `txnChecked` through `txnChecked_safe`).
* `lessorSt` carries what the backend's `Put`, `Txn` and `LeaseRevoke` need of the lessor (A9 F2,
  F6): every key's lease live (3b's `Txn.leasesLive`), the lessor's backend the options' `Backend`,
  its range deleter set and `kv`'s (`kvDelOk`, provisional with `kvOk`: what turns into 3c's
  `Lease.rdOk` per revocation through 3e's `Mvcc.mvccDeleter_rdOk`).
* `optsOk` carries the backends' post-lock hook contracts under the lent `R` (`hooksOk`, A9 F3,
  F6): the lessor's (`Lease.beHook`/`beHookRun` at the options' backend) and the auth store's
  (`Auth.authBeHook` of the options' backend's auth wrapper, which with `authSt`'s `Auth.authBeCur`
  at that wrapper is exactly what 3d's `AdminTriple` takes: lease-auth's request), each giving `R`
  back.
* `opStep_step` concludes `ownStep` (W0's `Step` without its refusal disjunct, A9 F4): the backend
  makes no refusal of its own, so a client learns that a valid write at auth off with no alarm is
  applied (`ReqApplyWrite`).

## Integration I5 (2026-11-09)

* `checksSane` dropped: W0's round 5 admits an inverted range's refusal (`State.invertedDeny`), and
  `opErr` now answers it as the permission cache does (`invRefused`, provisional for 3d's exact
  report), so `irrStep_step`, `opStep_step` and `applyStep_reach` hold without it.
* The credential: `IrrOp.userAdd`/`userChangePassword` carry W0's stored credential (round 5's
  `pwHash`); `IrrOp.ok` asks it be a hash of some password (what 3d's `storeNext_adm` takes),
  `opStep_userAdd`/`opStep_userChangePassword` and `opBody` relate it to the client's request.
* 3d's slots: `authOk`, `authSt` are transparent over 3d's `authStoreAt`, `authCur`, `tokFrom`;
  `authRead` and `lessorRead` are gone (`CheckTxnAuth` is over 3d's names and takes a read-only
  transaction); `authRecordFits` is replaced by `nextOk` (3d's `recordsFit` of the next state, with
  `authReached`, which 3d's `AdminTriple` takes), threaded through `uberApplier.Apply`, `dispatch`,
  `isUber_apply` and the backend's admin methods; `permReads` reports each check through `C`
  (`permReads_writer`, `permReads_reader` in `ApiResult.lean`).
* 3c's slots: `lessorOk`, `lessorSt` are transparent over `Lease.isLessor`, `Lease.lessorState`.
* Left provisional (owners have no such predicate yet): `kvOk`, `kvSt` (3e/2d: the apply thread's
  authority over `Mvcc.mvccState`, 3b's S6), `statusOk`, `snapSrvOk`, `ciOk`, `authnIdx` (2d),
  `irrDecodes`, `irrMsgAt`, `reqMsgAt` (3h), `invRefused` (3d). (`clusterVerOk` is transparent
  since the verify round, over 2e's `Membership.verFits`. Second pass: `statusOk`, `snapSrvOk`,
  `ciOk`, `authnIdx` are introduced by 2d's `EtcdServer.applyLent_opts`; `kvOk`, `kvSt`, `kvDelOk`
  by 2d's `EtcdServer.srvStores_kv`; their realizations are 2d's.)
* The coordinator's decisions (after the batch passes): a token provider's error (no-op provider
  always, JWT on signing) is admitted as the member's result for a token assignment the step
  answered (`IrrOp.isAuthn`, `provErrResult`, `replyAt_result`); a non-`nil` empty range end is out of
  the permission checks' scope (`nonissues/etcd-auth-empty-range-end-point-check.md`; since the
  recheck, RR3, carried by the request predicates themselves: W0's `txnReqOwn`/`requestOpOwn` give
  3h's `endsOk` at any ownership, so the separate `endsDecoded`/`opsDecoded` and
  `reqMsgAt_endsDecoded` are gone).

## Requirement snippets

`examples/specreq/apply/`: `apply.go` (`ReqApplyWrite`: a committed write's result is the step's
answer; `ReqApplyReplay`: the replay changes nothing and answers nil; `ReqApplyNoResult`: an
unregistered read is not applied), `alarm.go` (`ReqNoSpaceCapped`: after a `NOSPACE` alarm a put is
refused and nothing changes; `ReqCorrupt`), `auth.go` (`ReqStaleRevision`: a write with an old auth
revision is `ErrAuthOldRevision` and changes nothing; `ReqCheckTxnAuth`: the request path's check).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.State
public import SpecPlan.Spec.go_etcd_io.raft.v3.Model
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api
public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.apply
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.schema
public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.apply

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel Classical

/-! ## The member's configuration -/

/-- **A member's configuration, as far as its apply's answers depend on it**: the lessor's minimum
TTL (`minLeaseTTL`: 1.5 election timeouts, rounded up to a second; `server.go`). -/
structure MemberCfg where
  minLeaseTTL : Int

/-- A configuration etcd builds (`newServer`): a positive minimum TTL, at most `MaxLeaseTTL`. -/
def MemberCfg.ok (mc : MemberCfg) : Prop := 0 < mc.minLeaseTTL ∧ mc.minLeaseTTL ≤ maxLeaseTTL

/-! ## The decoded request -/

/-- `RequestHeader`: the proposer's request id, the user and the auth revision the request path
stamped (`""`, `0`: no user). -/
structure Hdr where
  id : w64
  username : GoString
  authRev : w64

/-- `AlarmRequest_AlarmAction`: `GET`, `ACTIVATE`, `DEACTIVATE`, or another value. -/
inductive AlarmAct where
  | get
  | activate
  | deactivate
  | other

/-- **What an `InternalRaftRequest` asks** (its one set field). -/
inductive IrrOp where
  /-- one of W0's client requests that go through raft (`reqIsIrr`) -/
  | req (rq : Req)
  /-- `AuthUserAdd` with the stored credential the request path computed (`HashedPassword` is its
  base64, `Auth.b64 hash`; W0's `pwHash pw hash` of the client's password, `IrrOp.ok`) -/
  | userAdd (name : GoString) (hash : Bytes) (noPassword : Bool)
  /-- `AuthUserChangePassword` with the credential -/
  | userChangePassword (name : GoString) (hash : Bytes)
  /-- `Authenticate` (`InternalAuthenticateRequest`): a token for `name` (the password the request
  path checked, unused by the apply), its simple-token prefix -/
  | authenticate (name password : GoString) (simpleToken : GoString)
  /-- `Alarm`: the action, the member, the raw `AlarmType` -/
  | alarm (act : AlarmAct) (memberId : Nat) (at' : w32)
  /-- `LeaseCheckpoint`: each lease's remaining TTL -/
  | leaseCheckpoint (cps : List (Int × Int))
  /-- `ClusterVersionSet` -/
  | clusterVersionSet (ver : GoString)
  /-- `ClusterMemberAttrSet` (`publishV3`) -/
  | memberAttrSet (id : Nat) (name : GoString) (urls : List GoString)
  /-- `DowngradeInfoSet` -/
  | downgradeInfoSet (enabled : Bool) (ver : GoString)
  /-- `DowngradeVersionTest` (tests only: ignored) -/
  | downgradeVersionTest

/-- **A decoded `InternalRaftRequest`**: its `ID`, its `Header` (absent in pre-3.0 entries), what
it asks. -/
structure Irr where
  id : w64
  hdr : Option Hdr
  op : IrrOp

/-- The W0 requests an `InternalRaftRequest` carries as such. -/
def reqIsIrr : Req → Bool
  | .range _ | .put _ | .deleteRange _ | .txn _ | .compact .. | .leaseGrant .. | .leaseRevoke _
  | .authEnable | .authDisable | .authStatus | .userGet _ | .userList | .userDelete _
  | .userGrantRole .. | .userRevokeRole .. | .roleAdd _ | .roleGet _ | .roleList | .roleDelete _
  | .roleGrantPermission .. | .roleRevokePermission .. => true
  | _ => false

/-- The request id `apply.Apply` returns: `ID`, or the header's when `ID` is `0`. -/
def Irr.reqId (ir : Irr) : w64 :=
  if ir.id ≠ W64 0 then ir.id else match ir.hdr with | some h => h.id | none => W64 0

/-- Whether `apply.Apply` finds an id (it panics otherwise: no `ID` and no header). -/
def Irr.hasId (ir : Irr) : Prop := ir.id ≠ W64 0 ∨ ir.hdr.isSome

/-- The auth layer's `authInfo` for the request: the header's user and revision, or none. -/
def Irr.user (ir : Irr) : GoString := match ir.hdr with | some h => h.username | none => []
def Irr.revW (ir : Irr) : w64 := match ir.hdr with | some h => h.authRev | none => W64 0
def Irr.authRev (ir : Irr) : Nat := uint.nat ir.revW

/-- The request's principal in W0's terms (2c's and 3d's): none only for no auth info at all (user
`""`, revision `0`); a client certificate with an empty common name stamps user `""` at a nonzero
revision (`AuthInfoFromTLS`), which is the principal `some ""` (Go answers `ErrPermissionDenied`:
no such user). -/
def Irr.who (ir : Irr) : Principal :=
  if ir.user = [] ∧ ir.authRev = 0 then none else some ir.user

/-- `needAdminPermission`. -/
def IrrOp.needAdmin : IrrOp → Bool
  | .req .authEnable | .req .authDisable | .userAdd .. | .req (.userDelete _)
  | .userChangePassword .. | .req (.userGrantRole ..) | .req (.userRevokeRole ..)
  | .req (.roleAdd _) | .req (.roleGrantPermission ..) | .req (.roleRevokePermission ..)
  | .req (.roleDelete _) | .req .userList | .req .roleList => true
  | _ => false

/-- `noSideEffect`: a range, a user or role read, the auth status. -/
def IrrOp.noSideEffect : IrrOp → Bool
  | .req (.range _) | .req (.userGet _) | .req (.roleGet _) | .req .authStatus => true
  | _ => false

/-- The membership requests (`dispatch`'s first switch: applied in both modes). -/
def IrrOp.isMembership : IrrOp → Bool
  | .clusterVersionSet _ | .memberAttrSet .. | .downgradeInfoSet .. | .downgradeVersionTest => true
  | _ => false

def IrrOp.isTxn : IrrOp → Bool
  | .req (.txn _) => true
  | _ => false

/-- A token assignment (`Authenticate`'s apply), whose token provider may fail after the step
(`provErrResult`, `ApiResult.lean`). -/
def IrrOp.isAuthn : IrrOp → Bool
  | .authenticate .. => true
  | _ => false

/-! ## The gates -/

-- A transaction puts somewhere (either branch, any nesting): `BackendQuota.Cost` is positive.
mutual
def RequestOp.hasPut : RequestOp → Bool
  | .put _ => true
  | .txn _ succ fail => RequestOp.hasPutL succ || RequestOp.hasPutL fail
  | _ => false
def RequestOp.hasPutL : List RequestOp → Bool
  | [] => false
  | op :: ops => RequestOp.hasPut op || RequestOp.hasPutL ops
end

/-- The requests the corrupt applier refuses (`corrupt.go`). -/
def IrrOp.corruptRefused : IrrOp → Bool
  | .req (.range _) | .req (.put _) | .req (.deleteRange _) | .req (.txn _) | .req (.compact ..)
  | .req (.leaseGrant ..) | .req (.leaseRevoke _) => true
  | _ => false

/-- The requests the capped applier refuses (`capped.go`): a put, a transaction with a put, a grant. -/
def IrrOp.cappedRefused : IrrOp → Bool
  | .req (.put _) | .req (.leaseGrant ..) => true
  | .req (.txn t) => RequestOp.hasPutL t.success || RequestOp.hasPutL t.failure
  | _ => false

/-- The quota applier's writes (`quota.go`): a put, a transaction, a grant. -/
def IrrOp.quotaWrite : IrrOp → Bool
  | .req (.put _) | .req (.txn _) | .req (.leaseGrant ..) => true
  | _ => false

/-- An alarm of kind `k` is raised. -/
def hasAlarm (σ : State) (k : AlarmKind) : Prop := ∃ a ∈ σ.alarms, a.kind = k

/-- The layers of an applier (from the outermost). -/
inductive Layer where
  | corrupt
  | capped
  | auth
  | quota
  | backend

/-- The base chain (`newApplierV3`): auth over quota over backend. -/
def baseLayers : List Layer := [.auth, .quota, .backend]

/-- **The chain the raised alarms select** (`restoreAlarms`). -/
def chainLayers (σ : State) : List Layer :=
  (if hasAlarm σ .corrupt then [.corrupt] else []) ++
  (if hasAlarm σ .nospace then [.capped] else []) ++ baseLayers

/-- One permission check of the auth applier: an operation's range, or the keys of a lease a put
names or a revocation revokes (`checkLeasePuts`). -/
inductive Check where
  | op (t : PermType) (rng : KeyRange)
  | lease (id : Int)

/-- `IsAdminPermitted` (no revision check). -/
def adminErr (a : AuthState) (u : GoString) : Option EtcdErr :=
  if a.enabled = false then none
  else if u = [] then some .userEmpty
  else match a.users u with
    | none => some .userNotFound
    | some ur => if rootRole ∈ ur.roles then none else some .permissionDenied

/-- `isOpPermitted`'s checks before the user's permissions: auth on, a revision, not older than the
store's, an existing user. -/
def preErr (a : AuthState) (u : GoString) (rev : Nat) : Option EtcdErr :=
  if a.enabled = false then none
  else if rev = 0 then some .userEmpty
  else if rev < a.rev then some .authOldRevision
  else if a.users u = none then some .permissionDenied
  else none

/-- (provisional, 3d's) **The permission cache built from `a` refuses `u`'s operation `t` on the
inverted range `rng`** (`checkKeyInterval`: `adt`'s `Contains` of an empty interval, a function of
the cache that the model leaves open: W0's `State.invertedDeny` allows either answer). 3d's
`checkPost` is asked to report it exactly at the cache's state (`notes/specs-only/integration-I5.md`). -/
opaque invRefused (a : AuthState) (u : GoString) (t : PermType) (rng : KeyRange) : Prop

/-- `isOpPermitted` (`IsRangePermitted`, `IsPutPermitted`, `IsDeleteRangePermitted`): an inverted
range (`Auth.rngInverted`: W0's `KeyRange.inverted` with a non-empty key) passes or not as the cache
answers (`invRefused`); W0's `State.invertedDeny` admits the refusal. -/
def opErr (a : AuthState) (u : GoString) (rev : Nat) (t : PermType) (rng : KeyRange) :
    Option EtcdErr :=
  match preErr a u rev with
  | some e => some e
  | none => if a.enabled = false ∨ a.isRoot u ∨
                (a.covers u t rng ∧ (Auth.rngInverted rng → ¬ invRefused a u t rng)) then none
            else some .permissionDenied

/-- `checkLeasePuts`: nothing for a lease the lessor does not have or an administrator; else each
attached key's write permission (the keys in any order: every failure is the same error). -/
def leaseErr (σ : State) (u : GoString) (rev : Nat) (id : Int) : Option EtcdErr :=
  if σ.leases id = none ∨ adminErr σ.auth u = none ∨ ¬ (∃ k, σ.attached id k) then none
  else match preErr σ.auth u rev with
    | some e => some e
    | none => if ∀ k, σ.attached id k → σ.auth.covers u .write { key := k, rangeEnd := [] }
              then none else some .permissionDenied

def checkErr (σ : State) (u : GoString) (rev : Nat) : Check → Option EtcdErr
  | .op t rng => opErr σ.auth u rev t rng
  | .lease id => leaseErr σ u rev id

/-- The first failing check. -/
def firstErr (σ : State) (u : GoString) (rev : Nat) : List Check → Option EtcdErr
  | [] => none
  | c :: cs => match checkErr σ u rev c with
    | some e => some e
    | none => firstErr σ u rev cs

/-- `checkPutAuth`: the key's write, the lease's keys, the key's read for a `prevKv`. -/
def putChecks (p : PutReq) : List Check :=
  [.op .write { key := p.key, rangeEnd := [] }, .lease p.lease] ++
  (if p.prevKv then [.op .read { key := p.key, rangeEnd := [] }] else [])

-- `checkTxnPermission`, `checkTxnReqsPermission`: the comparisons' reads, then each operation of
-- the success branch, then the failure branch (a delete's `prevKv` read before its write).
mutual
def RequestOp.checks : RequestOp → List Check
  | .empty => []
  | .range r => [.op .read r.range]
  | .put p => putChecks p
  | .deleteRange d => (if d.prevKv then [.op .read d.range] else []) ++ [.op .write d.range]
  | .txn cmps succ fail => cmps.map (fun c => .op .read c.range) ++ RequestOp.checksL succ ++
      RequestOp.checksL fail
def RequestOp.checksL : List RequestOp → List Check
  | [] => []
  | op :: ops => RequestOp.checks op ++ RequestOp.checksL ops
end

/-- **The auth applier's own check of a request** (`authApplierV3`'s `Put`, `Range`,
`DeleteRange`, `Txn`, `LeaseRevoke`, `UserGet`, `RoleGet`), at the auth info `u`, `rev`. -/
def authErr (σ : State) (u : GoString) (rev : Nat) : IrrOp → Option EtcdErr
  | .req (.put p) => firstErr σ u rev (putChecks p)
  | .req (.range r) => firstErr σ u rev [.op .read r.range]
  | .req (.deleteRange d) => firstErr σ u rev
      ([.op .write d.range] ++ (if d.prevKv then [.op .read d.range] else []))
  | .req (.txn t) => firstErr σ u rev (RequestOp.checks (RequestOp.txn t.compare t.success t.failure))
  | .req (.leaseRevoke id) => firstErr σ u rev [.lease id]
  | .req (.userGet n) =>
      match adminErr σ.auth u with
      | some e => if n ≠ u then some e else none
      | none => none
  | .req (.roleGet r) =>
      match adminErr σ.auth u with
      | some e => if (∃ ur, σ.auth.users u = some ur ∧ r ∈ ur.roles) then none else some e
      | none => none
  | _ => none

/-- **The refusals of the layers `ls`**, outermost first. -/
def layersErr (σ : State) (u : GoString) (rev : Nat) (op : IrrOp) : List Layer → Option EtcdErr
  | [] => none
  | .corrupt :: ls => if op.corruptRefused then some .corrupt else layersErr σ u rev op ls
  | .capped :: ls => if op.cappedRefused then some .noSpace else layersErr σ u rev op ls
  | .auth :: ls => match authErr σ u rev op with
      | some e => some e
      | none => layersErr σ u rev op ls
  | .quota :: ls => layersErr σ u rev op ls
  | .backend :: _ => none

/-! ## The backend's operation -/

/-- **What the backend applier does** with a request that passed the gates (a client request, a
hashed user change, a token, a checkpoint): opaque, a function (see the header and its laws). -/
opaque opStep (mc : MemberCfg) (σ : State) (op : IrrOp) (σ' : State) (res : Resp) : Prop

/-- The placeholder answer of a request that answers nothing (a membership request, a checkpoint,
the replay): the `Result`'s `Resp` and `Err` are `nil`. -/
def noAns : Resp := .ok (.alarm [])

/-- A member's attributes published (W0's `EnvStep.publish`; nothing for a removed member). -/
def publish (σ : State) (id : Nat) (name : GoString) (urls : List GoString) : State :=
  { σ with members := σ.members.map (fun m =>
      if m.id = id then { m with name := name, clientURLs := urls } else m) }

/-- **An alarm action** (`applierV3backend.Alarm`, then `restoreAlarms`). -/
def alarmStep (σ : State) (act : AlarmAct) (mid : Nat) (at' : w32) (σ' : State) (res : Resp) :
    Prop :=
  match act with
  | .get => σ' = σ ∧ res = .ok (.alarm (V3alarm.getOf σ.alarms at'))
  | .activate =>
      if at' = W32 0 then σ' = σ ∧ res = .ok (.alarm [])
      else ∃ k, V3alarm.kindOf at' = some k ∧
        σ' = { σ with alarms := V3alarm.raise σ.alarms ⟨mid, k⟩ } ∧ res = .ok (.alarm [⟨mid, k⟩])
  | .deactivate =>
      match V3alarm.kindOf at' with
      | some k =>
          if ∃ b ∈ σ.alarms, V3alarm.sameAlarm ⟨mid, k⟩ b then
            σ' = { σ with alarms := V3alarm.clear σ.alarms ⟨mid, k⟩ } ∧ res = .ok (.alarm [⟨mid, k⟩])
          else σ' = σ ∧ res = .ok (.alarm [])
      | none => σ' = σ ∧ res = .ok (.alarm [])
  | .other => σ' = σ ∧ res = noAns

/-- **The step of the layers `ls`** on a request past the membership switch: their refusal, or
the backend's operation. -/
def layersStep (mc : MemberCfg) (σ : State) (u : GoString) (rev : Nat) (op : IrrOp)
    (ls : List Layer) (σ' : State) (res : Resp) : Prop :=
  match layersErr σ u rev op ls with
  | some e => σ' = σ ∧ res = .err e
  | none =>
    match op with
    | .alarm act mid at' => alarmStep σ act mid at' σ' res
    | .leaseCheckpoint _ => σ' = σ ∧ res = noAns
    | _ => opStep mc σ op σ' res

/-- **Applying `ir`** at a member configured `mc` from the model state `σ`, with `v3`
(`shouldApplyV3`): see the header. -/
def irrStep (mc : MemberCfg) (σ : State) (ir : Irr) (v3 : Bool) (σ' : State) (res : Resp) : Prop :=
  match (if ir.op.needAdmin then adminErr σ.auth ir.user else none) with
  | some e => σ' = σ ∧ res = .err e
  | none =>
    if ir.op.isMembership then
      res = noAns ∧
      σ' = (match ir.op with
            | .memberAttrSet id name urls => if v3 then publish σ id name urls else σ
            | _ => σ)
    else if v3 = false then σ' = σ ∧ res = noAns
    else layersStep mc σ ir.user ir.authRev ir.op (chainLayers σ) σ' res

/-- (provisional, 3h's) **The bytes `bs` decode to an `InternalRaftRequest` carrying `ir`**
(`pbutil.MustUnmarshalMessage` succeeds: protobuf's limits included, `IrrBody.depthOk`), with
**exactly one** of the known request fields set (`needAdminPermission`, `noSideEffect` and
`dispatch` test them in different orders). -/
opaque irrDecodes (bs : List w8) (ir : Irr) : Prop

/-- **The apply's model of a committed normal entry** (2d's `applyStep`, same signature): an empty
entry changes nothing; otherwise its request's `irrStep` with `v3`. -/
def applyStep (mc : MemberCfg) (σ : State) (e : Raft.LogEntry) (σ' : State) (res : Resp) : Prop :=
  e.type = Raft.EntryNormal ∧
  ((e.data = [] ∧ σ' = σ ∧ res = noAns) ∨
   (e.data ≠ [] ∧ ∃ ir, irrDecodes e.data ir ∧ irrStep mc σ ir true σ' res))

/-! ## Admission and the panic-free requests -/

/-- **A cluster version every member's apply accepts**: `semver.MustParse` parses it, and the
parsed version fits the member's binary (2e's `Membership.verFits`: `RaftCluster.SetVersion`'s
`MustDetectDowngrade` and `Version`'s re-parse do not panic). Verify round (server-boot's request):
was a provisional opaque. -/
def clusterVerOk (ver : GoString) : Prop :=
  ∃ sv, Semver.parse ver = some sv ∧ Membership.verFits sv

/-- A transaction the gRPC layer admits, in W0's terms: valid, every run of either branch puts
each key at most once, and no ignore-put follows a delete covering its key (3b's `Txn.txnSafe`:
`txn.put` indexes the previous value an ignore-put reads, `put.go:55`, a panic after the delete,
`issues/etcd-txn-delete-then-ignore-put.md`); `checkIntervals` refuses both (2a's `txnChecked`
gives them: 2c's `txnChecked_safe`, and the law asked of 2c in `repair-apply-txn.md`). -/
def txnAdmitted (t : TxnReq) : Prop :=
  t.valid ∧ Txn.txnSafe t ∧ ∀ (h : KVHist) s0 lv R s evs rs ops, (ops = t.success ∨ ops = t.failure) →
    TxnRun h s0 lv R ops (s0, []) (.ok (s, evs, rs)) → putOnce evs

/-- **A request the request path proposes** (the gRPC layer's validation, the server's chosen lease
id; a compaction's revision nonzero, W0's scope, which 3e's `KV.Compact` takes): the refinement
laws' premise. -/
def reqAdmitted : Req → Prop
  | .range r => r.key ≠ [] ∧ r.validSort
  | .put p => p.invalid = none
  | .deleteRange d => d.key ≠ []
  | .txn t => txnAdmitted t
  | .leaseGrant id _ => id ≠ 0
  | .compact rev _ => rev ≠ 0
  | _ => True

/-- **A request's own step** (W0's `Step` without its refusal disjunct, at `lo = 0`): what the
backend applier does with a request the gates let through (`opStep_step`). -/
def ownStep (who : Principal) (rq : Req) (σ σ' : State) (res : Resp) : Prop :=
  kvStep who rq σ σ' res ∨ leaseStep who rq σ σ' res ∨ authStep who rq σ σ' res ∨
    clusterStep who rq σ σ' res

/-- **The requests a member applies without panicking** (with `irrDecodes` and `Irr.hasId`), as
the request path proposes them: an admitted client request, a user's credential that is a hash of
some password (W0's `pwHash`: the proposer hashed the client's password; what makes the stored
credential W0's, `Auth.storeNext_adm`), an alarm action on a known type (`AlarmStore.Activate` of
another type is outside the model), a cluster version the members accept. The auth records' fit
(3d's `Auth.recordsFit`) is a fact of the next state: the apply thread's `nextOk`. A member's
attributes need the member known: the caller's `memberUpd`. -/
def IrrOp.ok (op : IrrOp) : Prop :=
  match op with
  | .req rq => reqIsIrr rq = true ∧ reqAdmitted rq
  | .userAdd _ h np => np = false → ∃ pw, pwHash pw h
  | .userChangePassword _ h => ∃ pw, pwHash pw h
  | .alarm .activate m at' => m < 2 ^ 64 ∧ (at' = W32 0 ∨ V3alarm.kindOf at' ≠ none)
  | .alarm _ m _ => m < 2 ^ 64
  | .clusterVersionSet ver => clusterVerOk ver
  | _ => True

/-- **A state the cluster can be in** (W0's `etcdLb_init` gives it of every recorded state): the
pure facts the refinement laws need follow from it (lease `0` never live, no key naming a dead
lease, no user with the empty name). -/
def reachable (σ : State) : Prop := ∃ ms : List Member, Reach (State.init ms) σ

/-! ## TTL variants -/

/-- `σ` with every lease's TTL erased. -/
def eraseTTL (σ : State) : State :=
  { σ with leases := fun i => (σ.leases i).map (fun _ => { ttl := 0 }),
           leaseHist := σ.leaseHist.map (fun t i => (t i).map (fun _ => { ttl := 0 })) }

/-- **Two states that differ at most in their leases' TTLs** (two members configured differently). -/
def ttlEq (σ₁ σ₂ : State) : Prop := eraseTTL σ₁ = eraseTTL σ₂

/-- Two answers that differ at most in a grant's TTL. -/
def respTtlEq : Resp → Resp → Prop
  | .ok (.leaseGrant i _), .ok (.leaseGrant i' _) => i = i'
  | r, r' => r = r'

/-! ## The answer a result carries -/

-- A transaction's answers with every range's contents dropped (`SkipRangeExecution`: the header's
-- revision kept).
mutual
def OpResp.skip : OpResp → OpResp
  | .range rev _ => .range rev { kvs := [], more := false, count := 0 }
  | .txn ok rs => .txn ok (OpResp.skipL rs)
  | r => r
def OpResp.skipL : List OpResp → List OpResp
  | [] => []
  | r :: rs => OpResp.skip r :: OpResp.skipL rs
end

def skipRanges : Resp → Resp
  | .ok (.txn rev ok rs) => .ok (.txn rev ok (OpResp.skipL rs))
  | r => r

/-- **The answer `res'` a member's result carries for the step's answer `res`** (see the header):
`res` (its ranges skipped for a skipping wrapper), an alarm list in another order, or the quota's
`ErrNoSpace` after a write it applied. -/
def resMatch (op : IrrOp) (sk : Bool) (res res' : Resp) : Prop :=
  res' = (if sk then skipRanges res else res) ∨
  (∃ l l', res = .ok (.alarm l) ∧ res' = .ok (.alarm l') ∧ l'.Perm l) ∨
  (op.quotaWrite = true ∧ (∃ b, res = .ok b) ∧ res' = .err .noSpace)

/-! ## Resources -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
  [hG : HeapGS HasLC.hasLC GF] [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`ua` is an uber-applier** of a member configured `mc` (see the header). Persistent. -/
opaque isUber [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ua : GoInterface) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames)
    (R : IProp GF) : IProp GF := iprop(True)

/-- **The state machine behind `ua` is at `σ`.** Exclusive. -/
opaque smAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ua : GoInterface) (σ : State) : IProp GF := iprop(True)

/-- **`ua` was built over the options `o`** (`NewUberApplier`'s; persistent): what gets the
stores back out of `smAt` (`smAt_optsSt`, `smAt_alarms`). -/
opaque uberOpts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ua : GoInterface) (o : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) :
    IProp GF := iprop(True)

/-- **The membership update an apply of `op` makes**: for a member's attributes, the caller's
atomic update of the view (2e's `clusterSt γc`) from a view that knows the member (a member or
removed) to the view with its attributes set, committing `Q`; `Q` itself for any other request. -/
def memberUpd (γc : Membership.CNames) (op : IrrOp) (Q : IProp GF) : IProp GF :=
  match op with
  | .memberAttrSet id name urls =>
      iprop(AU <{ ∃∃ (st : Membership.ClusterSt), Membership.clusterSt γc st ∗
              ⌜st.isMember id ∨ id ∈ st.removed⌝ }> @ ⊤, ∅
        <{ Membership.clusterSt γc
             (st.update id (fun m => { m with name := name, clientURLs := urls })), COMM Q }>)
  | _ => Q

/-! ### The options (`ApplierOptions`): the constructor's slots -/

/-- (provisional, 3e's and 2d's) **mvcc's `KV` `kv`**, whose write transactions run the backend's
post-lock hook with the apply thread's lent `R`. Persistent. Intended: `∃ γ γl q B Pk, Mvcc.isMvcc kv
γ ∗ Mvcc.mvccLessorIs γ γl ∗ Mvcc.mvccBackend γ q B Pk` with `Pk` the hook's contract under `R`. -/
opaque kvOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (kv : GoInterface) (R : IProp GF) : IProp GF := iprop(True)

/-- (provisional, 3e's and 2d's) **`kv`'s store is at the history `h`** (the apply thread's, its
only writer). Exclusive. Intended: the writer's half of an authority over `Mvcc.mvccState γ σ₀` with
`σ₀.kv = h ∧ σ₀.pending = []`, whose other half the server's invariant holds while 2c's readers fire
their updates on `mvccState` (3b's S6: the pinned update txn's writes take); 2d's to define. -/
opaque kvSt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (kv : GoInterface) (h : KVHist) : IProp GF := iprop(True)

/-- **The lessor `le`** (3c's `Lease.isLessor`), with minimum TTL `mc.minLeaseTTL`. Persistent. -/
def lessorOk (le : GoInterface) (mc : MemberCfg) : IProp GF :=
  iprop(∃ (p : Loc) (γl : Lease.Names) (c : Lease.Cfg), ⌜le = Lease.lessorIface p ∧
    c.minTTL = mc.minLeaseTTL⌝ ∗ Lease.isLessor p γl c)

/-- (provisional, 3e's and 2d's, with `kvOk`) **`rd` is the range deleter of `kv`'s store, for a
lessor named `γl` persisting to `be`** (persistent): what the apply thread turns into 3c's
`Lease.rdOk γl rd n ls P D Q` at each revocation, with `P` the store's writer resources (`kvSt`,
`kvOk`'s backend and hook under `R`). Intended realization: at `kvOk kv R`'s store `γ` and storage
`B`, `⌜be = GoInterface.ok (Mvcc.storageVal B)⌝ ∗ Mvcc.mvccDeleter rd γ ∗ Mvcc.mvccLessorIs γ γl ∗
□ (Mvcc.kbHeld B ∗-∗ Lease.beTxHeld be)` (3e's `Mvcc.mvccDeleter_rdOk`'s premises; the last is 4a's
`Backend.leaseTxHeld_intro`). Introduced with `kvOk` and `kvSt` by 2d's `EtcdServer.srvStores_kv`
(from `NewStore`'s post, which sets the deleter, `kvstore.go:117`/`watchable_store.go:107`; after a
snapshot, the server's closure `func() lease.TxnDelete { return s.kv.Write(…) }` that
`applySnapshot` passes to `lessor.Recover`, `server.go:1087`, over `s.kv`; verify-round cleanup,
RR-grpc-auth: was "`applySnapshot`'s new store"). -/
opaque kvDelOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (kv : GoInterface) (γl : Lease.Names) (be : GoInterface) (rd : GoFunc) :
    IProp GF := iprop(True)

/-- **`le`'s live leases are `lt`, each attached to the keys of the store `s` that name it** (3c's
writer token `Lease.lessorState`: its table `lt`, its `itemMap` the store's lease fields, each live
lease's item set its keys), **every key's lease live** (3b's `Txn.leasesLive`: mvcc's `Attach` of a
dead lease panics, so `txn.Put`/`txn.Txn` take it; true of every reachable state), persisting to the
backend `be` (the options' `Backend`: the server passes `s.be` to both, `server.go:344,1193`; after
a snapshot, `Recover`'s new backend and the new options'), its range deleter set and `kv`'s
(`kvDelOk`: `Revoke`'s `Lease.rdOk`). Exclusive. -/
def lessorSt (le kv be : GoInterface) (lt : Int → Option LeaseRec) (s : EtcdModel.Store) :
    IProp GF :=
  iprop(∃ (p : Loc) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat) (ls : Lease.LessorState),
    ⌜le = Lease.lessorIface p ∧ ls.table = lt ∧
      (∀ k, ls.items k = match s k with | some r => r.lease | none => 0) ∧
      (∀ id e, ls.leases id = some e → ∀ k, ls.keys e.obj k ↔ ls.items k = id) ∧
      Txn.leasesLive s ls ∧ ls.be = be ∧ ls.rd ≠ func.nil⌝ ∗
    kvDelOk kv γl be ls.rd ∗ Lease.isLessor p γl c ∗ Lease.lessorState γl n ls)

/-- **The auth store `ast`** (3d's `Auth.authStoreAt`), its tokens registered in W0's `γ`
(`tokenUser`). Persistent. -/
def authOk (ast : GoInterface) (γ : Cluster) : IProp GF :=
  iprop(∃ (st : Loc) (γa : Auth.AuthNames), ⌜ast = interface.mkOk (go.GoType.PointerType
    go_etcd_io.etcd.server.v3.auth.authStore.ty) #st⌝ ∗ Auth.authStoreAt st γ γa)

/-- **`ast`'s state is `a`** (3d's writer `Auth.authCur`, with the simple provider's token right
`Auth.tokFrom`: the apply thread is the only writer), **its current backend the wrapper of `be`**
(3d's `Auth.authBeCur` at the `*authBackend` that 4b's `schema.NewAuthBackend(lg, be)` built: the
options' `Backend`, as the server passes `s.be` to both, `server.go:369,1193`; `Recover` moves it to
a snapshot's, `server.go:1127`, before the new options are built). Exclusive. With `hooksOk`'s
`authBeHook` producer at that wrapper, it is what 3d's `AdminTriple` (and `AuthEnable`,
`AuthDisable`, `HasRole`) take and give back (verify round: lease-auth's request; re-review A9 N1:
3d's `authHook`/`authHook_intro` are gone). -/
def authSt (ast be : GoInterface) (a : AuthState) : IProp GF :=
  iprop(∃ (st : Loc) (γ : Cluster) (γa : Auth.AuthNames) (i n : Nat) (abe : Loc) (lg : Loc),
    ⌜ast = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty) #st⌝ ∗
    Auth.authStoreAt st γ γa ∗ Auth.authCur γa i a ∗ Auth.tokFrom γa n ∗
    Auth.authBeCur γa (interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) #abe) ∗
    (abe ↦□ go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg : IProp GF))

/-- (2d's: introduced by `EtcdServer.applyLent_opts`) **The raft status getter `rs`** (the `*EtcdServer`): `MemberID`, `Leader`,
`Term` safe to call (any answer). Persistent. -/
opaque statusOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rs : GoInterface) : IProp GF := iprop(True)

/-- (2d's: introduced by `EtcdServer.applyLent_opts`) **The snapshot server `ss`**: `ForceSnapshot()` with `R`, given back.
Persistent. Intended: `ss` the `*EtcdServer` `s` and `R ⊢ EtcdServer.forceSnapW s ∗ ...` (2d's
`EtcdServer.ForceSnapshot.spec`). -/
opaque snapSrvOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ss : GoInterface) (R : IProp GF) : IProp GF := iprop(True)

/-- (2d's: introduced by `EtcdServer.applyLent_opts`) **The consistent indexer `ci`**: `ConsistentIndex()` with `R` (any answer).
Persistent. -/
opaque ciOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ci : GoInterface) (R : IProp GF) : IProp GF := iprop(True)

/-- (internal) **Permission checks of the auth info `u`, `rev` through the auth store `ast` and
the lessor `le`, with `A` lent, each reported by `C`**: every check (`isOpPermitted` of an operation's range; for a lease, the
lessor's `Lookup` and `Keys`, `IsAdminPermitted`, `IsPutPermitted` per key) runs without panicking
and its answer `err` satisfies `C c err`; a lease's check only if `L`. Persistent. Its two instances
are laws (`ApiResult.lean`): the apply thread's (`permReads_writer`: `A` the stores at `σ`, `C` the
exact `checkErr σ`), the request path's (`permReads_reader`: `A` nothing, `C` 3d's `checkPost` from
a lower bound, no lease checks). -/
opaque permReads [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ast le : GoInterface) (u : GoString) (rev : w64) (A : IProp GF) (L : Bool)
    (C : Check → GoInterface → IProp GF) : IProp GF := iprop(True)

/-- A check of a lease's keys. -/
def Check.isLease : Check → Bool
  | .lease _ => true
  | .op .. => false

/-- (2d's: introduced by `EtcdServer.applyLent_opts`, for every `name`, `tok`) **The apply
thread's token index for `Authenticate`** (persistent): under the lent `R`, `ConsistentIndex()`
answers the index `idx` of the entry being applied, a nonzero `uint64` (`0 < idx < 2 ^ 64`), and
**if that entry asks `Authenticate(name, tok)`**, the prefix `tok` has no `.` (the proposer's
`GenTokenPrefix`: letters) and the cluster `γ` issued the simple token `tok ++ "." ++ idx`
(decimal) to `name`
(`tokenUser`, 2d's: the committed entry), `idx` above every `Authenticate` index applied before
(3d's `tokFrom`, held in `authSt`). Conditional (second pass, server-core's request): an
unconditional reading is false for any other name, and `applyLent_opts` gives it for all; the
applier uses it at the entry it is applying, whose request is `.authenticate name _ tok`. The two
facts on `idx` and `tok` are what 3d's `Auth.authnCtx γ ctx name idx` asks beside the `tokenUser`
(`0 < idx ∧ idx < 2 ^ 64 ∧ '.' ∉ tok`; re-review A9 S1, as 2d's `applyLent_opts` now states). What 3d's `Auth.authnCtx γ ctx name idx` (transparent: the two `ctxValIs` that
`context.WithValue` gives, and this `tokenUser`) and `Auth.tokFrom` need at
`applierV3backend.Authenticate`. -/
opaque authnIdx [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (R : IProp GF) (γ : Cluster) (name tok : GoString) : IProp GF := iprop(True)

/-- **The apply thread's facts about the next state** of a step `S` (from 2d's committed entry: the
history point after it): every state `σ'` the step may move to has its auth state reached by the
cluster (3d's `Auth.authReached`) and fitting bbolt (3d's `Auth.recordsFit`, a scope restriction:
`issues/etcd-auth-useradd-long-name-fatal.md`); for a token assignment, its index right
(`authnIdx`). What 3d's `AdminTriple` and `Authenticate` take. Persistent. -/
def nextOk (γ : Cluster) (R : IProp GF) (op : IrrOp) (S : State → Prop) : IProp GF :=
  iprop(□ (∀ σ', ⌜S σ'⌝ -∗ Auth.authReached γ σ'.auth ∗ ⌜Auth.recordsFit σ'.auth⌝) ∗
    match op with
    | .authenticate name _ tok => authnIdx R γ name tok
    | _ => True)

/-- **The backends' post-lock hook contracts, lent `R`** (persistent): the lessor's batch
transaction (`Grant`, `Checkpoint`: 3c's `Lease.beHook be Pk f ∗ Lease.beHookRun be Pk f Pre Q ∗
(Q ={⊤}=∗ Pk ∗ Post)`) at the backend `be`, and the auth store's (3d's `Auth.authBeHook abe Pre Q`
of any auth backend wrapping `be`, `schema.NewAuthBackend`'s `*authBackend`, which the admin
methods' `AdminTriple` takes directly with the store's `authBeCur`, `authSt`),
each run from the apply thread's `R` and giving `R` back. The hook is the server's
`getTxPostLockInsideApplyHook` (`server.go:409,1098`: the consistent index saved under the lock,
which the lent `R` owns), proved once over 4a's `Backend.hookRun` at every share; the lessor's half
by 4a's `Backend.leaseBeHook_intro`/`leaseHookRun_intro`, the auth half by 4a's introduction of
`Auth.authBeHook` (requested of 4a by lease-auth). -/
def hooksOk (be : GoInterface) (R : IProp GF) : IProp GF :=
  iprop((∃ (Pk Q : IProp GF) (f : GoFunc), Lease.beHook be Pk f ∗
      □ Lease.beHookRun be Pk f R Q ∗ □ (Q ={⊤}=∗ Pk ∗ R)) ∗
    □ ∀ (abe lg : Loc),
      (abe ↦□ go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg : IProp GF) -∗
      ∃ Q : IProp GF, □ Auth.authBeHook (interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) #abe) R Q ∗
        □ (Q ={⊤}=∗ R))

/-- **The options' handles** (`NewUberApplier`'s persistent premise): the logger, mvcc's KV, the
lessor at `mc`, the auth store registering in `γ`, the membership with view `γc`, the backend for
the quota, the raft status, the snapshot server and the consistent indexer under `R`, the
backends' post-lock hook contracts under `R` (`hooksOk`), and the server's invariant over the
view's cluster version (2e's `Membership.clusterVerInv γc`: `ClusterVersionSet`'s `Version` and
`SetVersion`, `DowngradeInfoSet`'s `SetDowngradeInfo` fire their updates in it). -/
def optsOk (o : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (mc : MemberCfg)
    (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) : IProp GF :=
  iprop(Zap.isLogger o.Logger' ∗ kvOk o.KV' R ∗ lessorOk o.Lessor' mc ∗ authOk o.AuthStore' γ ∗
    (∃ cid lid, Membership.isCluster o.Cluster' γc cid lid) ∗ ServerStorage.beReadable o.Backend' ∗
    statusOk o.RaftStatus' ∗ snapSrvOk o.SnapshotServer' R ∗ ciOk o.ConsistentIndex' R ∗
    hooksOk o.Backend' R ∗ Membership.clusterVerInv γc)

/-- **The options' stores at the model state `σ`** (`NewUberApplier`'s exclusive premise, `smAt`'s
content): mvcc at `σ.kv`, the lessor at `σ.leases` attached by `σ.kv.store` (persisting to the
options' backend, its deleter `o.KV'`'s), the auth store at `σ.auth`, the alarm store at
`σ.alarms`, the backend's member buckets at `σ.members` and its stored cluster version and
downgrade info (2e's `Membership.beVer`, outside the model: any). -/
def optsSt (o : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (σ : State) :
    IProp GF :=
  iprop(kvSt o.KV' σ.kv ∗ lessorSt o.Lessor' o.KV' o.Backend' σ.leases σ.kv.store ∗ authSt o.AuthStore' o.Backend' σ.auth ∗
    (∃ γa, V3alarm.isAlarmStore o.AlarmStore' γa ∗ V3alarm.alarmSt γa σ.alarms) ∗
    (∃ st : Membership.ClusterSt, Membership.beView o.Cluster' st ∗ ⌜st.members.Perm σ.members⌝) ∗
    (∃ v : Membership.VerSt, Membership.beVer o.Cluster' v))

/-! ### Internal (the package's own specs) -/

/-- The backend applier at `b`, over its options (internal). Persistent. -/
opaque beAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (b : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) :
    IProp GF := iprop(True)

/-- Backend applier `b`'s stores at `σ` (internal; `smAt`'s content). Exclusive. -/
opaque stAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (b : Loc) (σ : State) : IProp GF := iprop(True)

/-- **The applier `v` is the layers `ls` over backend applier `b`**, its auth layer `aa`
(internal). Persistent. -/
opaque applierAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (v : GoInterface) (ls : List Layer) (b aa : Loc) : IProp GF := iprop(True)

/-- The backend applier `b`'s options are `o` (its read-only field, internal). -/
def beOpts (b : Loc) (o : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) : IProp GF :=
  iprop(b.[go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend, go!"options"] ↦□ o)

/-- **`p` is an `*uberApplier`** over backend applier `b` and auth layer `aa` (internal): its
read-only fields, its `applyV3base` the base chain. Persistent. -/
opaque uberAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames)
    (R : IProp GF) : IProp GF := iprop(True)

/-- `p.applyV3` holds the chain of layers `ls` (internal). Exclusive. -/
opaque uberChain [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (ls : List Layer) : IProp GF := iprop(True)

/-- The auth layer `aa`'s `authInfo` is `(u, rev)`, owned (its mutex held; internal). -/
opaque aiAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (aa : Loc) (u : GoString) (rev : w64) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`p` is an `InternalRaftRequest` carrying `ir`**, read-only. Persistent. -/
opaque irrMsgAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (ir : Irr) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`p` is the request message of `op`'s kind** (`*pb.PutRequest`, ...,
`*membershippb.ClusterVersionSetRequest`), read-only. Persistent. -/
opaque reqMsgAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (op : IrrOp) : IProp GF := iprop(True)

/-- **A wrapper of `ir`** (`*InternalRaftRequestWrapper`), skipping the ranges if `sk`. -/
def wrapperAt (r : Loc) (ir : Irr) (sk : Bool) : IProp GF :=
  iprop(∃ p : Loc,
    r.[go_etcd_io.etcd.server.v3.etcdserver.apply.InternalRaftRequestWrapper, go!"InternalRaftRequest"] ↦□ p ∗
    r.[go_etcd_io.etcd.server.v3.etcdserver.apply.InternalRaftRequestWrapper, go!"SkipRangeExecution"] ↦□ sk ∗
    irrMsgAt p ir)

/-- **A method's reply** `(resp, err)` for `op` answered `res` (the `*pb.<Kind>Response` with its
header, or the error of `res`): `ApiResult.lean` relates it to 2c's `applyResult` (internal). -/
opaque replyAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (op : IrrOp) (res : Resp) (resp : GoInterface) (err : GoInterface) :
    IProp GF := iprop(True)

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
  [hG : HeapGS HasLC.hasLC GF] [go_gctx : GoGlobalContext] [sem : go.Semantics]

def persistent.spec : Prop :=
  (∀ ua mc γ γc R, Persistent (isUber (GF := GF) ua mc γ γc R)) ∧
  (∀ b mc γ γc R, Persistent (beAt (GF := GF) b mc γ γc R)) ∧
  (∀ v ls b aa, Persistent (applierAt (GF := GF) v ls b aa)) ∧
  (∀ p b aa mc γ γc R, Persistent (uberAt (GF := GF) p b aa mc γ γc R)) ∧
  (∀ kv R, Persistent (kvOk (GF := GF) kv R)) ∧
  (∀ kv γl be rd, Persistent (kvDelOk (GF := GF) kv γl be rd)) ∧
  (∀ rs, Persistent (statusOk (GF := GF) rs)) ∧
  (∀ ss R, Persistent (snapSrvOk (GF := GF) ss R)) ∧ (∀ ci R, Persistent (ciOk (GF := GF) ci R)) ∧
  (∀ ast le u rev A L C, Persistent (permReads (GF := GF) ast le u rev A L C)) ∧
  (∀ R γ n t, Persistent (authnIdx (GF := GF) R γ n t)) ∧
  (∀ p ir, Persistent (irrMsgAt (GF := GF) p ir)) ∧
  (∀ p op, Persistent (reqMsgAt (GF := GF) p op))

def smAt_timeless.spec : Prop := ∀ ua σ, Timeless (smAt (GF := GF) ua σ)

/-- **The stores back out of the state machine** (giving up the applier: `applySnapshot` recovers
them, then builds a new one with `NewUberApplier`). -/
def smAt_optsSt.spec : Prop :=
  ∀ ua o σ, uberOpts (GF := GF) ua o ∗ smAt ua σ ⊢ optsSt o σ

/-- **The alarm store's view, lent out of the state machine** (`applyEntryNormal`'s
`alarmStore.Get(NOSPACE)` while the apply thread holds `smAt`). -/
def smAt_alarms.spec : Prop :=
  ∀ ua o σ, uberOpts (GF := GF) ua o ∗ smAt ua σ ⊢
    ∃ γa, V3alarm.isAlarmStore o.AlarmStore' γa ∗ V3alarm.alarmSt γa σ.alarms ∗
      (V3alarm.alarmSt γa σ.alarms -∗ smAt ua σ)

def uberOpts_persistent.spec : Prop := ∀ ua o, Persistent (uberOpts (GF := GF) ua o)

def smAt_excl.spec : Prop := ∀ ua σ σ', smAt (GF := GF) ua σ ∗ smAt ua σ' ⊢ iprop(False)

/-- (internal) The state machine of an `*uberApplier` is its chain at the alarms' selection and its
backend applier's stores. -/
def smAt_unfold.spec : Prop :=
  ∀ (p b aa : Loc) mc γ γc R (σ : State), uberAt (GF := GF) p b aa mc γ γc R ⊢
    (smAt (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p) σ ∗-∗
      uberChain p (chainLayers σ) ∗ stAt b σ)

/-- (provisional with `irrMsgAt`, 3h's) **The entry's decoded request is a read-only message**
(`irrMsgAt`'s realization: `Unmarshal`'s `*InternalRaftRequest`, never written after): what 3h's
`EtcdServerPb.stringerAt_irr` needs for `dispatch`'s `&pb.InternalRaftStringer{Request: r}`
(`uber_applier.go:99,101`). Second pass (grpc-v3rpc's `stringerAt_irr`). Recheck (RR4): with its
nesting below `Proto.depthMax`, which `stringerAt_irr` takes: the realization's content is
`MustUnmarshalMessage`'s, which the bytes encode (`irrDecodes`: protobuf's limits included, so some
content of depth below `depthMax` encodes them), hence of that depth (`encodes_fun`, `norm_facts`). -/
def irrMsgAt_msg.spec : Prop := ∀ p ir,
  irrMsgAt (GF := GF) p ir ⊢
    ∃ c, Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.InternalRaftRequest.ty p DFrac.discard c ∗
      ⌜Proto.depth c < Proto.depthMax⌝

def aiAt_excl.spec : Prop := ∀ aa u u' r r', aiAt (GF := GF) aa u r ∗ aiAt aa u' r' ⊢ iprop(False)

end laws

/-! ### The model's laws (pure) -/

/-- A message decodes to one request. -/
def irrDecodes_fun.spec : Prop := ∀ bs ir ir', irrDecodes bs ir → irrDecodes bs ir' → ir = ir'

/-- **The backend's operation is a function** of the configuration, the state and the request. -/
def opStep_fun.spec : Prop :=
  ∀ mc σ op σ₁ σ₂ r₁ r₂, opStep mc σ op σ₁ r₁ → opStep mc σ op σ₂ r₂ → σ₁ = σ₂ ∧ r₁ = r₂

/-- **It is defined** for every request a member applies without panicking. -/
def opStep_total.spec : Prop := ∀ mc σ op, op.ok → ∃ σ' res, opStep mc σ op σ' res

/-- **A client request's operation is its own step of W0's model** by any principal the gates let
through (the auth layer passed: `layersErr` none at the chain the alarms select), for an admitted
request at a configuration etcd builds: never one of `Step`'s refusals (the backend's errors are
mvcc's, the lessor's and the auth store's, each inside its request's step; verify-round A9 F4). -/
def opStep_step.spec : Prop :=
  ∀ (mc : MemberCfg) σ (ir : Irr) rq σ' res, mc.ok → ir.op = .req rq → ir.op.ok → reachable σ →
    (ir.op.needAdmin = true → adminErr σ.auth ir.user = none) →
    layersErr σ ir.user ir.authRev ir.op (chainLayers σ) = none →
    opStep mc σ (.req rq) σ' res → ownStep ir.who rq σ σ' res

/-- A token assignment changes nothing: the token, or `ErrAuthNotEnabled`, `ErrAuthFailed` (no such
user, or one without a password). The answer is the model's: the token provider's own failure (the
no-op provider always, JWT on a signing error) is not a step's answer but the member's result's
(`provErrResult`, `replyAt_result`; the coordinator's decision, integration I5), at the same state. -/
def opStep_authenticate.spec : Prop :=
  ∀ mc σ name pw tok σ' res, opStep mc σ (.authenticate name pw tok) σ' res →
    σ' = σ ∧ (σ.auth.enabled = false ∧ res = .err .authNotEnabled ∨
      σ.auth.enabled = true ∧ (∀ ur, σ.auth.users name = some ur → ur.password = none) ∧
        res = .err .authFailed ∨
      σ.auth.enabled = true ∧ (∃ ur, σ.auth.users name = some ur ∧ ur.password ≠ none) ∧
        res = .ok .authenticate)

/-- **A user added with the credential `h`** is W0's addition of any password `h` is a hash of
(W0's round 5: `userAdd` stores some `cred` with `pwHash pw cred`; here `cred = h`), by a caller who
may make it. -/
def opStep_userAdd.spec : Prop :=
  ∀ mc σ name h np σ' res, opStep mc σ (.userAdd name h np) σ' res →
    ∀ pw, (np = false → pwHash pw h) →
    ∀ who, σ.auth.mayCall who (.userAdd name pw np) → authStep who (.userAdd name pw np) σ σ' res

/-- **A password changed to the credential `h`**: W0's change to any password `h` is a hash of. -/
def opStep_userChangePassword.spec : Prop :=
  ∀ mc σ name h σ' res, opStep mc σ (.userChangePassword name h) σ' res →
    ∀ pw, pwHash pw h →
    ∀ who, σ.auth.mayCall who (.userChangePassword name pw) →
      authStep who (.userChangePassword name pw) σ σ' res

/-- **Two members configured differently, at TTL-variant states, apply alike up to TTLs; with one
configuration, the same answer** (no answer reads a stored TTL: a grant's is the request's raised
to the minimum). -/
def opStep_ttl.spec : Prop :=
  ∀ mc₁ mc₂ σ₁ σ₂ op σ₁' σ₂' r₁ r₂, ttlEq σ₁ σ₂ →
    opStep mc₁ σ₁ op σ₁' r₁ → opStep mc₂ σ₂ op σ₂' r₂ → ttlEq σ₁' σ₂' ∧ respTtlEq r₁ r₂ ∧
      (mc₁ = mc₂ → r₁ = r₂)

/-- **The backend never answers a stale auth revision** (its stores' own errors only). -/
def opStep_noOldRev.spec : Prop := ∀ mc σ op σ', ¬ opStep mc σ op σ' (.err .authOldRevision)

/-- **A read's operation changes nothing.** -/
def opStep_read.spec : Prop :=
  ∀ mc σ op σ' res, op.noSideEffect = true → opStep mc σ op σ' res → σ' = σ

/-! ### Consequences (laws of the model, for 2c and 2d) -/

/-- The apply of a request is a function. -/
def irrStep_fun.spec : Prop :=
  ∀ mc σ ir v3 σ₁ σ₂ r₁ r₂, irrStep mc σ ir v3 σ₁ r₁ → irrStep mc σ ir v3 σ₂ r₂ →
    σ₁ = σ₂ ∧ r₁ = r₂

/-- **The apply of an entry is a function** (2d's `applyStep_fun`). -/
def applyStep_fun.spec : Prop :=
  ∀ mc σ e (σ₁ σ₂ : State) (r₁ r₂ : Resp),
    applyStep mc σ e σ₁ r₁ → applyStep mc σ e σ₂ r₂ → σ₁ = σ₂ ∧ r₁ = r₂

/-- **Every entry a member applies without panicking has a step.** -/
def applyStep_total.spec : Prop :=
  ∀ mc σ (e : Raft.LogEntry) ir, e.type = Raft.EntryNormal → e.data ≠ [] → irrDecodes e.data ir →
    ir.op.ok → ∃ σ' res, applyStep mc σ e σ' res

/-- **A client request's apply is a `Step` of W0's model by its principal**: its refusals
(`ErrCorrupt`, `ErrNoSpace`, `ErrAuthOldRevision`, `ErrUserEmpty`), its permission errors, its
operation (2c's commit-time firing), at a reachable state (lease `0` never live, keys name live
leases, no user `""`); an inverted range's refusal is W0's `invertedDeny`. -/
def irrStep_step.spec : Prop :=
  ∀ (mc : MemberCfg) σ (ir : Irr) rq σ' res, mc.ok → ir.op = .req rq → ir.op.ok → reachable σ →
    irrStep mc σ ir true σ' res → Step ir.who rq σ σ' res

/-- **An alarm action is W0's step**: `GET` of every type (`NONE`) is `alarmList`, `DEACTIVATE`
and `ACTIVATE` of a known kind are `alarmDisarm` and `alarmActivate` (by any principal: no
administrator check at the apply; W0's admin refusal is the request path's). -/
def irrStep_alarm.spec : Prop :=
  ∀ mc σ (ir : Irr) σ' res,
    irrStep mc σ ir true σ' res →
    (∀ m, ir.op = .alarm .get m (W32 0) → Step ir.who .alarmList σ σ' res) ∧
    (∀ m at' k, ir.op = .alarm .deactivate m at' → V3alarm.kindOf at' = some k →
      Step ir.who (.alarmDisarm ⟨m, k⟩) σ σ' res) ∧
    (∀ m at' k, ir.op = .alarm .activate m at' → m < 2 ^ 64 → V3alarm.kindOf at' = some k →
      Step ir.who (.alarmActivate ⟨m, k⟩) σ σ' res)

/-- **A read changes nothing** (`noSideEffect`: a range, a user or role read, the auth status), in
any state and mode. -/
def irrStep_read.spec : Prop :=
  ∀ mc σ (ir : Irr) v3 σ' res, ir.op.noSideEffect = true → irrStep mc σ ir v3 σ' res → σ' = σ

/-- **The history is one `Reach` sequence** (2d's `applyStep_reach`): applying an entry the
request path proposes, at a reachable state, moves to a state reachable from it (a client
request's `Step`, possibly with the hash in a password's place; an environment step; or nothing). -/
def applyStep_reach.spec : Prop :=
  ∀ mc σ (e : Raft.LogEntry) ir σ' res, mc.ok → reachable σ → irrDecodes e.data ir → ir.op.ok →
    applyStep mc σ e σ' res → Reach σ σ'

/-- **An alarm activation or a member's publication is an environment step, or nothing.** -/
def irrStep_env.spec : Prop :=
  ∀ (cfg : EnvCfg) mc σ (ir : Irr) σ' res,
    ((∃ m at', ir.op = .alarm .activate m at' ∧ m < 2 ^ 64) ∨
     (∃ id n u, ir.op = .memberAttrSet id n u)) →
    irrStep mc σ ir true σ' res → σ' = σ ∨ EnvStep cfg σ σ'

/-- **The requests invisible to the model change nothing**: a checkpoint, a token, a cluster
version, the downgrade info, the test request. -/
def irrStep_quiet.spec : Prop :=
  ∀ mc σ (ir : Irr) v3 σ' res,
    ((∃ c, ir.op = .leaseCheckpoint c) ∨ (∃ n pw t, ir.op = .authenticate n pw t) ∨
     (∃ v, ir.op = .clusterVersionSet v) ∨ (∃ b v, ir.op = .downgradeInfoSet b v) ∨
     ir.op = .downgradeVersionTest) →
    irrStep mc σ ir v3 σ' res → σ' = σ

/-- **The replay below the consistent index changes nothing.** -/
def irrStep_noV3.spec : Prop := ∀ mc σ ir σ' res, irrStep mc σ ir false σ' res → σ' = σ

/-- **A stale auth revision changes nothing**: an answer `ErrAuthOldRevision` leaves the state. -/
def irrStep_oldRev.spec : Prop :=
  ∀ mc σ ir v3 σ', irrStep mc σ ir v3 σ' (.err .authOldRevision) → σ' = σ

/-- **One configuration on TTL-variant states gives the same answer** (2d's round-1b item 1: the
proposer's replica is a TTL-variant of the history). -/
def applyStep_ttl_same.spec : Prop :=
  ∀ mc σ₁ σ₂ e σ₁' σ₂' r₁ r₂, ttlEq σ₁ σ₂ →
    applyStep mc σ₁ e σ₁' r₁ → applyStep mc σ₂ e σ₂' r₂ → ttlEq σ₁' σ₂' ∧ r₁ = r₂

/-- **Members configured differently stay TTL-variants** of each other. -/
def irrStep_ttl.spec : Prop :=
  ∀ mc₁ mc₂ σ₁ σ₂ ir v3 σ₁' σ₂' r₁ r₂, ttlEq σ₁ σ₂ →
    irrStep mc₁ σ₁ ir v3 σ₁' r₁ → irrStep mc₂ σ₂ ir v3 σ₂' r₂ → ttlEq σ₁' σ₂' ∧ respTtlEq r₁ r₂

end Apply
end EtcdGrove
end Perennial
