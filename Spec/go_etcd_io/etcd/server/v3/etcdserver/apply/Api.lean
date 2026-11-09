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
store's (3d). Its meaning is fixed by its laws: it is a `Step` of W0's model (`opStep_step`, for an
admitted request: the gRPC layer's validation passed, `reqAdmitted`), it changes nothing for a token
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
* `memberUpd γc ir Q` (transparent): for a member's attributes, the caller's atomic update of the
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
`σ.members`; `granted`, `leaseHist` ghost. `aiAt aa ai`: `aa.authInfo ↦ ai` (the mutex's
invariant is `∃ ai, aa.authInfo ↦ ai`).

## Laws

`isUber_persistent`, `smAt_excl`, `smAt_timeless`; the model: `irrDecodes_fun`, `opStep_fun`,
`opStep_total`, `opStep_step`, `opStep_authenticate`, `opStep_userAdd`, `opStep_userChangePassword`,
`opStep_ttl`, and the consequences 2c and 2d use, stated as laws (provable from the definitions and
the laws above): `irrStep_fun`, `applyStep_fun`, `applyStep_total`, `irrStep_step` (a client request's
apply is a `Step` of W0 by its principal), `irrStep_env` (an alarm or a publication is an `EnvStep`
or nothing), `irrStep_quiet` (a checkpoint, a token, a version, a downgrade: nothing),
`irrStep_noV3`, `irrStep_oldRev` (a stale auth revision changes nothing), `irrStep_ttl`.

## Requirement snippets

`examples/specreq/apply/`: `apply.go` (`ReqApplyWrite`: a committed write's result is the step's
answer; `ReqApplyReplay`: the replay changes nothing and answers nil; `ReqApplyNoResult`: an
unregistered read is not applied), `alarm.go` (`ReqNoSpaceCapped`: after a `NOSPACE` alarm a put is
refused and nothing changes; `ReqCorrupt`), `auth.go` (`ReqStaleRevision`: a write with an old auth
revision is `ErrAuthOldRevision` and changes nothing; `ReqCheckTxnAuth`: the request path's check).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.State
public import Spec.go_etcd_io.raft.v3.Model
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_uber_org.zap.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.apply
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.apply

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
  /-- `AuthUserAdd` with the request path's hash of the password (`HashedPassword`) -/
  | userAdd (name : GoString) (hash : Bytes) (noPassword : Bool)
  /-- `AuthUserChangePassword` with the hash -/
  | userChangePassword (name : GoString) (hash : Bytes)
  /-- `Authenticate` (`InternalAuthenticateRequest`): a token for `name`, its simple-token prefix -/
  | authenticate (name : GoString) (simpleToken : GoString)
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
def Irr.authRev (ir : Irr) : Nat := match ir.hdr with | some h => uint.nat h.authRev | none => 0

/-- The request's principal in W0's terms. -/
def Irr.who (ir : Irr) : Principal := if ir.user = [] then none else some ir.user

/-- A header the request path stamps (`AuthInfoFromCtx`): a user exactly when a revision. The
refinement laws need it (a user with revision `0` is `ErrUserEmpty` in Go, a denial in W0). -/
def Irr.hdrOk (ir : Irr) : Prop := ir.user = [] ↔ ir.authRev = 0

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

/-- `isOpPermitted` (`IsRangePermitted`, `IsPutPermitted`, `IsDeleteRangePermitted`). -/
def opErr (a : AuthState) (u : GoString) (rev : Nat) (t : PermType) (rng : KeyRange) :
    Option EtcdErr :=
  match preErr a u rev with
  | some e => some e
  | none => if a.enabled = false ∨ a.isRoot u ∨ a.covers u t rng then none
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
(`pbutil.MustUnmarshalMessage` succeeds: protobuf's limits included, `IrrBody.depthOk`), with one of
the known fields set. -/
opaque irrDecodes (bs : List w8) (ir : Irr) : Prop

/-- **The apply's model of a committed normal entry** (2d's `applyStep`, same signature): an empty
entry changes nothing; otherwise its request's `irrStep` with `v3`. -/
def applyStep (mc : MemberCfg) (σ : State) (e : Raft.LogEntry) (σ' : State) (res : Resp) : Prop :=
  e.type = Raft.EntryNormal ∧
  ((e.data = [] ∧ σ' = σ ∧ res = noAns) ∨
   (e.data ≠ [] ∧ ∃ ir, irrDecodes e.data ir ∧ irrStep mc σ ir true σ' res))

/-! ## Admission and the panic-free requests -/

/-- (provisional, 3d's) **An auth record the store can write**: the user and role names and the
user record fit bbolt's key and value limits (`issues/etcd-auth-useradd-long-name-fatal.md`: a
longer name makes the backend exit). -/
opaque authRecordFits (op : IrrOp) : Prop

/-- (provisional, 2e's: membership and `version`) **A cluster version every member's apply
accepts**: `semver.MustParse` parses it, and the member's binary is not older
(`MustDetectDowngrade`). -/
opaque clusterVerOk (ver : GoString) : Prop

/-- A transaction the gRPC layer admits, in W0's terms: valid, and every run of either branch puts
each key at most once (`checkIntervals`, 2a's `txnChecked` gives it). -/
def txnAdmitted (t : TxnReq) : Prop :=
  t.valid ∧ ∀ (h : KVHist) s0 lv R s evs rs ops, (ops = t.success ∨ ops = t.failure) →
    TxnRun h s0 lv R ops (s0, []) (.ok (s, evs, rs)) → putOnce evs

/-- **A request the request path proposes** (the gRPC layer's validation, the server's chosen lease
id): the refinement laws' premise. -/
def reqAdmitted : Req → Prop
  | .range r => r.key ≠ [] ∧ r.validSort
  | .put p => p.invalid = none
  | .deleteRange d => d.key ≠ []
  | .txn t => txnAdmitted t
  | .leaseGrant id _ => id ≠ 0
  | _ => True

/-- **The requests a member applies without panicking** (with `irrDecodes` and `Irr.hasId`): an
admitted client request, records that fit, an alarm action on a known type (`AlarmStore.Activate`
of another type is outside the model), a cluster version the members accept. A member's
attributes need the member known: the caller's `memberUpd`. -/
def IrrOp.ok (op : IrrOp) : Prop :=
  match op with
  | .req rq => reqIsIrr rq = true ∧ reqAdmitted rq ∧ authRecordFits op
  | .userAdd .. | .userChangePassword .. => authRecordFits op
  | .alarm .activate _ at' => at' = W32 0 ∨ V3alarm.kindOf at' ≠ none
  | .clusterVersionSet ver => clusterVerOk ver
  | _ => True

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
opaque isUber (ua : GoInterface) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames)
    (R : IProp GF) : IProp GF := iprop(True)

/-- **The state machine behind `ua` is at `σ`.** Exclusive. -/
opaque smAt (ua : GoInterface) (σ : State) : IProp GF := iprop(True)

/-- **The membership update an apply of `ir` makes**: for a member's attributes, the caller's
atomic update of the view (2e's `clusterSt γc`) from a view that knows the member (a member or
removed) to the view with its attributes set, committing `Q`; `Q` itself for any other request. -/
def memberUpd (γc : Membership.CNames) (ir : Irr) (Q : IProp GF) : IProp GF :=
  match ir.op with
  | .memberAttrSet id name urls =>
      iprop(AU <{ ∃∃ (st : Membership.ClusterSt), Membership.clusterSt γc st ∗
              ⌜st.isMember id ∨ id ∈ st.removed⌝ }> @ ⊤, ∅
        <{ Membership.clusterSt γc
             (st.update id (fun m => { m with name := name, clientURLs := urls })), COMM Q }>)
  | _ => Q

/-! ### The options (`ApplierOptions`): the constructor's slots -/

/-- (provisional, 3e's) **mvcc's `KV` `kv`**, whose write transactions run the backend's post-lock
hook with the apply thread's lent `R`. Persistent. -/
opaque kvOk (kv : GoInterface) (R : IProp GF) : IProp GF := iprop(True)

/-- (provisional, 3e's) **`kv`'s store is at the history `h`** (the apply thread's, its only
writer). Exclusive. -/
opaque kvSt (kv : GoInterface) (h : KVHist) : IProp GF := iprop(True)

/-- (provisional, 3c's) **The lessor `le`**, with minimum TTL `mc.minLeaseTTL`. Persistent. -/
opaque lessorOk (le : GoInterface) (mc : MemberCfg) : IProp GF := iprop(True)

/-- (provisional, 3c's) **`le`'s live leases are `lt`**, each attached to the keys of the store `s`
that name it. Exclusive. -/
opaque lessorSt (le : GoInterface) (lt : Int → Option LeaseRec) (s : EtcdModel.Store) : IProp GF :=
  iprop(True)

/-- (provisional, 3d's) **The auth store `ast`**, its tokens registered in W0's `γ` (`tokenUser`).
Persistent. -/
opaque authOk (ast : GoInterface) (γ : Cluster) : IProp GF := iprop(True)

/-- (provisional, 3d's) **`ast`'s state is `a`** (the apply thread is its only writer). Exclusive. -/
opaque authSt (ast : GoInterface) (a : AuthState) : IProp GF := iprop(True)

/-- (provisional, 2d's) **The raft status getter `rs`** (the `*EtcdServer`): `MemberID`, `Leader`,
`Term` safe to call (any answer). Persistent. -/
opaque statusOk (rs : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 2d's) **The snapshot server `ss`**: `ForceSnapshot()` with `R`, given back.
Persistent. -/
opaque snapSrvOk (ss : GoInterface) (R : IProp GF) : IProp GF := iprop(True)

/-- (provisional, 2d's) **The consistent indexer `ci`**: `ConsistentIndex()` with `R` (any answer).
Persistent. -/
opaque ciOk (ci : GoInterface) (R : IProp GF) : IProp GF := iprop(True)

/-- **The options' handles** (`NewUberApplier`'s persistent premise): the logger, mvcc's KV, the
lessor at `mc`, the auth store registering in `γ`, the membership with view `γc`, the backend for
the quota, the raft status, the snapshot server and the consistent indexer under `R`. -/
def optsOk (o : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (mc : MemberCfg)
    (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) : IProp GF :=
  iprop(Zap.isLogger o.Logger' ∗ kvOk o.KV' R ∗ lessorOk o.Lessor' mc ∗ authOk o.AuthStore' γ ∗
    (∃ cid lid, Membership.isCluster o.Cluster' γc cid lid) ∗ ServerStorage.beReadable o.Backend' ∗
    statusOk o.RaftStatus' ∗ snapSrvOk o.SnapshotServer' R ∗ ciOk o.ConsistentIndex' R)

/-- **The options' stores at the model state `σ`** (`NewUberApplier`'s exclusive premise, `smAt`'s
content): mvcc at `σ.kv`, the lessor at `σ.leases` attached by `σ.kv.store`, the auth store at
`σ.auth`, the alarm store at `σ.alarms`, the backend's member buckets at `σ.members`. -/
def optsSt (o : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (σ : State) :
    IProp GF :=
  iprop(kvSt o.KV' σ.kv ∗ lessorSt o.Lessor' σ.leases σ.kv.store ∗ authSt o.AuthStore' σ.auth ∗
    (∃ γa, V3alarm.isAlarmStore o.AlarmStore' γa ∗ V3alarm.alarmSt γa σ.alarms) ∗
    (∃ st : Membership.ClusterSt, Membership.beView o.Cluster' st ∗ ⌜st.members.Perm σ.members⌝))

/-! ### Internal (the package's own specs) -/

/-- The backend applier at `b`, over its options (internal). Persistent. -/
opaque beAt (b : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) :
    IProp GF := iprop(True)

/-- Backend applier `b`'s stores at `σ` (internal; `smAt`'s content). Exclusive. -/
opaque stAt (b : Loc) (σ : State) : IProp GF := iprop(True)

/-- **The applier `v` is the layers `ls` over backend applier `b`**, its auth layer `aa`
(internal). Persistent. -/
opaque applierAt (v : GoInterface) (ls : List Layer) (b aa : Loc) : IProp GF := iprop(True)

/-- **`p` is an `*uberApplier`** over backend applier `b` and auth layer `aa` (internal): its
read-only fields, its `applyV3base` the base chain. Persistent. -/
opaque uberAt (p b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames)
    (R : IProp GF) : IProp GF := iprop(True)

/-- `p.applyV3` holds the chain of layers `ls` (internal). Exclusive. -/
opaque uberChain (p : Loc) (ls : List Layer) : IProp GF := iprop(True)

/-- The auth layer `aa`'s `authInfo` is `(u, rev)`, owned (its mutex held; internal). -/
opaque aiAt (aa : Loc) (u : GoString) (rev : w64) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`p` is an `InternalRaftRequest` carrying `ir`**, read-only. Persistent. -/
opaque irrMsgAt (p : Loc) (ir : Irr) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`p` is the request message of `op`'s kind** (`*pb.PutRequest`, ...,
`*membershippb.ClusterVersionSetRequest`), read-only. Persistent. -/
opaque reqMsgAt (p : Loc) (op : IrrOp) : IProp GF := iprop(True)

/-- **A wrapper of `ir`** (`*InternalRaftRequestWrapper`), skipping the ranges if `sk`. -/
def wrapperAt (r : Loc) (ir : Irr) (sk : Bool) : IProp GF :=
  iprop(∃ p : Loc,
    r.[go_etcd_io.etcd.server.v3.etcdserver.apply.InternalRaftRequestWrapper, go!"InternalRaftRequest"] ↦□ p ∗
    r.[go_etcd_io.etcd.server.v3.etcdserver.apply.InternalRaftRequestWrapper, go!"SkipRangeExecution"] ↦□ sk ∗
    irrMsgAt p ir)

/-- **A method's reply** `(resp, err)` for `op` answered `res` (the `*pb.<Kind>Response` with its
header, or the error of `res`): `ApiResult.lean` relates it to 2c's `applyResult` (internal). -/
opaque replyAt (γ : Cluster) (op : IrrOp) (res : Resp) (resp : GoInterface) (err : GoInterface) :
    IProp GF := iprop(True)

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
  [hG : HeapGS HasLC.hasLC GF] [go_gctx : GoGlobalContext]

def persistent.spec : Prop :=
  (∀ ua mc γ γc R, Persistent (isUber (GF := GF) ua mc γ γc R)) ∧
  (∀ b mc γ γc R, Persistent (beAt (GF := GF) b mc γ γc R)) ∧
  (∀ v ls b aa, Persistent (applierAt (GF := GF) v ls b aa)) ∧
  (∀ p b aa mc γ γc R, Persistent (uberAt (GF := GF) p b aa mc γ γc R)) ∧
  (∀ kv R, Persistent (kvOk (GF := GF) kv R)) ∧ (∀ le mc, Persistent (lessorOk (GF := GF) le mc)) ∧
  (∀ ast γ, Persistent (authOk (GF := GF) ast γ)) ∧ (∀ rs, Persistent (statusOk (GF := GF) rs)) ∧
  (∀ ss R, Persistent (snapSrvOk (GF := GF) ss R)) ∧ (∀ ci R, Persistent (ciOk (GF := GF) ci R)) ∧
  (∀ p ir, Persistent (irrMsgAt (GF := GF) p ir)) ∧
  (∀ p op, Persistent (reqMsgAt (GF := GF) p op))

def smAt_timeless.spec : Prop := ∀ ua σ, Timeless (smAt (GF := GF) ua σ)

def smAt_excl.spec : Prop := ∀ ua σ σ', smAt (GF := GF) ua σ ∗ smAt ua σ' ⊢ iprop(False)

/-- (internal) The state machine of an `*uberApplier` is its chain at the alarms' selection and its
backend applier's stores. -/
def smAt_unfold.spec : Prop :=
  ∀ (p b aa : Loc) mc γ γc R (σ : State), uberAt (GF := GF) p b aa mc γ γc R ⊢
    (smAt (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p) σ ∗-∗
      uberChain p (chainLayers σ) ∗ stAt b σ)

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

/-- **A client request's operation is a step of W0's model** by any principal the gates let
through (the auth layer passed: `layersErr` none at the chain the alarms select), for an admitted
request at a configuration etcd builds. -/
def opStep_step.spec : Prop :=
  ∀ (mc : MemberCfg) σ (ir : Irr) rq σ' res, mc.ok → ir.op = .req rq → ir.op.ok → ir.hdrOk →
    (ir.op.needAdmin = true → adminErr σ.auth ir.user = none) →
    layersErr σ ir.user ir.authRev ir.op (chainLayers σ) = none →
    opStep mc σ (.req rq) σ' res → Step ir.who rq σ σ' res

/-- A token assignment changes nothing: the token, or `ErrAuthNotEnabled`, `ErrAuthFailed` (no such
user, or one without a password). -/
def opStep_authenticate.spec : Prop :=
  ∀ mc σ name tok σ' res, opStep mc σ (.authenticate name tok) σ' res →
    σ' = σ ∧ (σ.auth.enabled = false ∧ res = .err .authNotEnabled ∨
      σ.auth.enabled = true ∧ (∀ ur, σ.auth.users name = some ur → ur.password = none) ∧
        res = .err .authFailed ∨
      σ.auth.enabled = true ∧ (∃ ur, σ.auth.users name = some ur ∧ ur.password ≠ none) ∧
        ∃ t, res = .ok (.authenticate t))

/-- A hashed user addition is W0's with the hash stored in the password's place (W0's model is asked
to keep the stored credential: `req/go_etcd_io_etcd_api_v3.md`, from 3a). -/
def opStep_userAdd.spec : Prop :=
  ∀ mc σ name h np σ' res, opStep mc σ (.userAdd name h np) σ' res →
    ∀ who, σ.auth.mayCall who (.userAdd name h np) → authStep who (.userAdd name h np) σ σ' res

def opStep_userChangePassword.spec : Prop :=
  ∀ mc σ name h σ' res, opStep mc σ (.userChangePassword name h) σ' res →
    ∀ who, σ.auth.mayCall who (.userChangePassword name h) →
      authStep who (.userChangePassword name h) σ σ' res

/-- **Two members configured differently, at TTL-variant states, apply alike up to TTLs.** -/
def opStep_ttl.spec : Prop :=
  ∀ mc₁ mc₂ σ₁ σ₂ op σ₁' σ₂' r₁ r₂, ttlEq σ₁ σ₂ →
    opStep mc₁ σ₁ op σ₁' r₁ → opStep mc₂ σ₂ op σ₂' r₂ → ttlEq σ₁' σ₂' ∧ respTtlEq r₁ r₂

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
operation (2c's commit-time firing). The state has no user with the empty name (W0's reachable
states). -/
def irrStep_step.spec : Prop :=
  ∀ (mc : MemberCfg) σ (ir : Irr) rq σ' res, mc.ok → ir.op = .req rq → ir.op.ok → ir.hdrOk →
    σ.auth.users [] = none →
    irrStep mc σ ir true σ' res → Step ir.who rq σ σ' res

/-- **An alarm activation or a member's publication is an environment step, or nothing.** -/
def irrStep_env.spec : Prop :=
  ∀ (cfg : EnvCfg) mc σ (ir : Irr) σ' res,
    ((∃ m at', ir.op = .alarm .activate m at') ∨ (∃ id n u, ir.op = .memberAttrSet id n u)) →
    irrStep mc σ ir true σ' res → σ' = σ ∨ EnvStep cfg σ σ'

/-- **The requests invisible to the model change nothing**: a checkpoint, a token, a cluster
version, the downgrade info, the test request. -/
def irrStep_quiet.spec : Prop :=
  ∀ mc σ (ir : Irr) v3 σ' res,
    ((∃ c, ir.op = .leaseCheckpoint c) ∨ (∃ n t, ir.op = .authenticate n t) ∨
     (∃ v, ir.op = .clusterVersionSet v) ∨ (∃ b v, ir.op = .downgradeInfoSet b v) ∨
     ir.op = .downgradeVersionTest) →
    irrStep mc σ ir v3 σ' res → σ' = σ

/-- **The replay below the consistent index changes nothing.** -/
def irrStep_noV3.spec : Prop := ∀ mc σ ir σ' res, irrStep mc σ ir false σ' res → σ' = σ

/-- **A stale auth revision changes nothing**: an answer `ErrAuthOldRevision` leaves the state. -/
def irrStep_oldRev.spec : Prop :=
  ∀ mc σ ir v3 σ', irrStep mc σ ir v3 σ' (.err .authOldRevision) → σ' = σ

/-- **Members configured differently stay TTL-variants** of each other. -/
def irrStep_ttl.spec : Prop :=
  ∀ mc₁ mc₂ σ₁ σ₂ ir v3 σ₁' σ₂' r₁ r₂, ttlEq σ₁ σ₂ →
    irrStep mc₁ σ₁ ir v3 σ₁' r₁ → irrStep mc₂ σ₂ ir v3 σ₂' r₂ → ttlEq σ₁' σ₂' ∧ respTtlEq r₁ r₂

end Apply
end EtcdGrove
end Perennial
