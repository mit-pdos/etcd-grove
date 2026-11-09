/-
# etcd as a client observes it: the pure model (batch W0, the anchor)

The meaning of every client-facing spec of the specs-only branch. Transparent: the model is spelled
out, no theorem about it is stated here (a fact a client needs about it is the client's to prove, or
a law of the API that owns the resource it is about). The resource that holds a model state, the
lower bounds on it and the environment's permission are in `State.lean`; the wire messages the client
and the server exchange, over these values, in `Wire.lean`.

## What is in the state

`State`: everything a client of etcd can observe through the v3 API, and nothing else.

* `kv : KVHist`: the revisioned key-value store with its **whole history** (`revs`: the events of
  revisions `2, 3, …, rev`; revision `1` is the empty store a new cluster starts with) and its
  **compaction revision** (`compacted`: reads below it fail with `ErrCompacted`). The history is
  kept in full, also below the compaction revision: it is ghost, and keeping it makes a stale
  member's reply (a serializable read) and a watch's events statable without a second notion of
  "past state". A key's record (`KeyRec`) has etcd's create and mod revisions, version, value and
  lease.
* `leases`: the live leases, each with the TTL it was granted (`LeaseRec`); `granted`, every lease
  id ever granted (append-only: what a stale member may still report). The keys attached to a
  lease are not stored: they are the keys whose record names it (`State.attached`).
  **Time is not modelled**: the remaining TTL of a lease is not part of the state, its expiry is an
  environment step (`EnvStep.leaseExpire`) that may happen at any time, and a keep-alive guarantees
  nothing about the lease's liveness (a deposed leader may still renew a lease the new leader has
  revoked: that is time-based safety, outside the model).
* `auth : AuthState`: enabled flag, auth revision, users (password, roles), roles (permissions).
  Tokens are not modelled: a client authenticates as a principal (`Principal`, a user name or
  none), and a request whose token is stale is retried by the client's interceptor and never takes
  effect (it is not a step; see `Step`).
* `members`: the cluster's members (id, name, peer and client URLs, learner flag).
* `alarms`: the raised alarms (member, `NOSPACE` or `CORRUPT`).

## Operations

`Req` mirrors the v3 RPCs' requests (their protobuf fields, `int64` fields as `Int`). `Step who rq σ
σ' res` is **the cluster's linearized effect of one request** by principal `who`: from `σ` to `σ'`,
answering `res`. It is a relation:

* the success and the deterministic failures of each RPC (`ErrKeyNotFound`, `ErrLeaseNotFound`,
  `ErrCompacted`, `ErrFutureRev`, `ErrPermissionDenied`, ...) as etcd's apply code computes them
  (`server/etcdserver/{txn,apply}`, `server/storage/mvcc`, `server/lease`, `server/auth`,
  `server/etcdserver/api/membership`), including etcd's quirks that a client can observe
  (`issues/etcd-range-sort-none-limit.md`: the limit pushed down before a sort with no order;
  `issues/etcd-range-keys-only-lease.md`: a keys-only read reports lease `0`;
  `issues/etcd-txn-empty-serializable.md`: a serializable read-only transaction, the empty one
  included, is answered from a member's possibly stale store);
* a **refusal** (`Step.refuse`): any request may be refused with an error of `EtcdErr.refusal`
  (too many requests, request too large, no space, ..., the validation errors of its kind), the
  state unchanged. A refusal is a linearized no-op: the cluster decided the request will never
  take effect;
* the choices the server makes (a lease's id when the client asks for `0`, the TTL a member grants,
  a new member's id, the stale revision a serializable read is answered at).

What is *not* a step: an error after which the request may still take effect (a timeout, the
leader lost, the context done, a transport error: `EtcdErr.indefinite` and the non-etcd errors).
The client's specs (`client/v3/Api.lean`) give no information on those.

`EnvStep cfg σ σ'`: the transitions no client call causes: a lease expires and the leader revokes it
(its keys deleted in one revision), the server's auto-compaction, an alarm raised, a member
publishing its name and client URLs. `Reach` is the reflexive-transitive closure of all steps.

## The error values

`EtcdErr`: rpctypes' client-facing errors (`api/v3/v3rpc/rpctypes/error.go`), one constructor each.
`EtcdErr.indefinite` the ones that do not settle whether the request took effect. The Go values a
client compares against (`err == rpctypes.ErrCompacted`) are `State.lean`'s `errVal`.
-/
module

public import Perennial.Golang.Defn.String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdModel

open Classical

/-! ## Keys and ranges -/

/-- A key: bytes. -/
abbrev Key := GoString
/-- A value: bytes. -/
abbrev Bytes := GoString

/-- Byte order of keys (Go's `bytes.Compare`). -/
def keyLt (a b : Key) : Prop := go.GoStringLt a b
def keyLe (a b : Key) : Prop := go.GoStringLe a b

/-- A range of keys as etcd's requests name one: `key` and `range_end`. An empty `rangeEnd` names
the single key `key`; `"\x00"` every key from `key` on; any other `rangeEnd` the half-open range
`[key, rangeEnd)` (empty if `rangeEnd ≤ key`). -/
structure KeyRange where
  key : Key
  rangeEnd : Bytes

/-- `k` is in the range `r`. -/
def KeyRange.mem (r : KeyRange) (k : Key) : Prop :=
  if r.rangeEnd = [] then k = r.key
  else if r.rangeEnd = [0#8] then keyLe r.key k
  else keyLe r.key k ∧ keyLt k r.rangeEnd

/-! ## The store and its history -/

/-- A key's record: what `mvccpb.KeyValue` carries besides the key. -/
structure KeyRec where
  createRev : Nat
  modRev : Nat
  version : Nat
  value : Bytes
  /-- `0`: no lease -/
  lease : Int

/-- A key-value as a reply carries one (`mvccpb.KeyValue`). -/
structure KV where
  key : Key
  createRev : Nat
  modRev : Nat
  version : Nat
  value : Bytes
  lease : Int

def KV.ofRec (k : Key) (r : KeyRec) : KV :=
  { key := k, createRev := r.createRev, modRev := r.modRev, version := r.version,
    value := r.value, lease := r.lease }

/-- One change of a revision (`mvccpb.Event` without the previous key-value): a key put with its
new record, or deleted. -/
inductive Event where
  | put (key : Key) (rec : KeyRec)
  | delete (key : Key)

/-- The key-values at one revision: each key's record, `none` if absent. -/
abbrev Store := Key → Option KeyRec

def Store.empty : Store := fun _ => none

def Store.applyEvent (s : Store) : Event → Store
  | .put k r => fun k' => if k' = k then some r else s k'
  | .delete k => fun k' => if k' = k then none else s k'

def Store.applyEvents (s : Store) (evs : List Event) : Store := evs.foldl Store.applyEvent s

/-- The present keys of `s` in the range `r`, sorted by key, as key-values. -/
def Store.rangeKVs (s : Store) (r : KeyRange) (l : List KV) : Prop :=
  l.Pairwise (fun a b => keyLt a.key b.key) ∧
  ∀ kv, kv ∈ l ↔ (r.mem kv.key ∧ s kv.key = some
    { createRev := kv.createRev, modRev := kv.modRev, version := kv.version, value := kv.value,
      lease := kv.lease })

/-- **The KV history.** -/
structure KVHist where
  /-- the events of revisions `2, 3, …`, each a non-empty list, in order -/
  revs : List (List Event)
  /-- the compaction revision: `0` if never compacted; reads below it fail -/
  compacted : Nat

/-- The current revision (`1` for a new cluster). -/
def KVHist.rev (h : KVHist) : Nat := h.revs.length + 1

/-- The store at revision `r` (`1 ≤ r ≤ rev`; the current store above `rev`). -/
def KVHist.storeAt (h : KVHist) (r : Nat) : Store :=
  (h.revs.take (r - 1)).foldl Store.applyEvents Store.empty

/-- The current store. -/
def KVHist.store (h : KVHist) : Store := h.storeAt h.rev

/-- The events of revision `r` (none for `r ≤ 1` or `r > rev`). -/
def KVHist.eventsAt (h : KVHist) (r : Nat) : List Event :=
  if 2 ≤ r then (h.revs[r - 2]?).getD [] else []

/-- A write's commit: a new revision with the events `evs`, or none if there are none. -/
def KVHist.commit (h : KVHist) (evs : List Event) : KVHist :=
  if evs = [] then h else { h with revs := h.revs ++ [evs] }

/-- A member's view of the history at revision `r ≤ rev`, its compaction revision `c` (a member
behind the cluster has applied neither the later revisions nor, possibly, the later compactions). -/
def KVHist.view (h : KVHist) (r c : Nat) : KVHist :=
  { revs := h.revs.take (r - 1), compacted := c }

/-- `v` is a view of `h` a member may be at: a prefix of the history, a compaction revision at most
`h`'s and at most its own revision. -/
def KVHist.IsView (h v : KVHist) : Prop :=
  1 ≤ v.rev ∧ v.rev ≤ h.rev ∧ v.compacted ≤ h.compacted ∧ v.compacted ≤ v.rev ∧
    v = h.view v.rev v.compacted

/-- The key an event changes. -/
def Event.key : Event → Key
  | .put k _ => k
  | .delete k => k

/-- **The compaction condition** (the user's, round 11 of the mvcc API,
`.claude/skills/spec/examples/watch-compaction.md`; the one statement of it that the client's watch
(1b's `watchStep`), the gRPC watch server (2b) and mvcc's watch (3f's `wStep`, `progStep`) cite):
every revision from `lo` up to `h`'s compaction revision changes each key at most once (vacuous
while the compaction revision is below `lo`). A compaction at a revision that changes a key twice
keeps only the key's last change there, so a watch reading that revision afterwards gets it alone
(`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`; through gRPC such a revision comes from
`issues/etcd-txn-check-intervals-sibling.md`). A watch's exactness holds under it; a client
discharges it from its workload (no transaction puts and deletes one key, the usual case) or from
a cluster that never compacts. -/
def exactFrom (h : KVHist) (lo : Nat) : Prop :=
  ∀ r : Nat, lo ≤ r → r ≤ h.compacted → ((h.eventsAt r).map Event.key).Nodup

/-! ## Leases -/

/-- A live lease: the TTL it was granted (seconds; at least the TTL asked). -/
structure LeaseRec where
  ttl : Int

/-! ## Auth -/

/-- `authpb.Permission_Type`. -/
inductive PermType where
  | read
  | write
  | readwrite

/-- A permission's range as the store accepts it (`isValidPermissionRange`): a key, and an end that
is empty, `"\x00"`, or above the key. -/
def KeyRange.validPerm (r : KeyRange) : Prop :=
  r.key ≠ [] ∧ (r.rangeEnd = [] ∨ r.rangeEnd = [0#8] ∨ keyLt r.key r.rangeEnd)

/-- An inverted range: a proper end at or below the key (no key in it; the store's interval tree
may still refuse it). -/
def KeyRange.inverted (r : KeyRange) : Prop :=
  r.rangeEnd ≠ [] ∧ r.rangeEnd ≠ [0#8] ∧ ¬ keyLt r.key r.rangeEnd

/-- A role's permission: a type and a key range. -/
structure Perm where
  permType : PermType
  range : KeyRange

/-- A user: its stored credential (the password's hash the request path computed; `none` for a user
added with `NoPassword`) and roles, in order. -/
structure UserRec where
  password : Option Bytes
  roles : List GoString

/-- **`cred` is a hash of `pw`** (bcrypt's `GenerateFromPassword`, at the proposer): opaque, trusted
(3d's boundary). -/
opaque pwHash (pw cred : Bytes) : Prop

/-- **`pw` matches the stored credential `cred`** (bcrypt's `CompareHashAndPassword`): opaque,
trusted; a hash matches its own password (`State.lean`'s `pwHash_match`), and nothing more is
assumed (bcrypt reads 72 bytes, hashes collide: `nonissues/etcd-auth-password-72-byte-prefix.md`). -/
opaque pwMatch (cred pw : Bytes) : Prop

/-- **The auth state.** -/
structure AuthState where
  enabled : Bool
  /-- the auth revision: bumped by every change of the users, roles or the enabled flag -/
  rev : Nat
  users : GoString → Option UserRec
  roles : GoString → Option (List Perm)

def rootUser : GoString := go!"root"
def rootRole : GoString := go!"root"

/-- A principal: the user a client authenticates as, or none. -/
abbrev Principal := Option GoString

/-- `u` has the root role. -/
def AuthState.isRoot (a : AuthState) (u : GoString) : Prop :=
  ∃ ur, a.users u = some ur ∧ rootRole ∈ ur.roles

/-- `p` grants an operation of type `t`. -/
def PermType.grants (p : PermType) (t : PermType) : Prop :=
  p = .readwrite ∨ p = t

/-- User `u`'s roles grant `t` on every key of `rng` (the union of the permitted ranges covers it,
as `rangePermCache` checks). -/
def AuthState.covers (a : AuthState) (u : GoString) (t : PermType) (rng : KeyRange) : Prop :=
  ∃ ur, a.users u = some ur ∧ ∀ k, rng.mem k →
    ∃ rl ∈ ur.roles, ∃ ps, a.roles rl = some ps ∧ ∃ p ∈ ps, p.permType.grants t ∧ p.range.mem k

/-! ## Members and alarms -/

/-- A member (`etcdserverpb.Member`). -/
structure Member where
  id : Nat
  name : GoString
  peerURLs : List GoString
  clientURLs : List GoString
  isLearner : Bool

/-- `etcdserverpb.AlarmType`. -/
inductive AlarmKind where
  | nospace
  | corrupt
  /-- an alarm type a client's `Alarm(ACTIVATE)` names that etcd has no meaning for -/
  | other (n : Int)

structure Alarm where
  memberId : Nat
  kind : AlarmKind

/-! ## The state -/

/-- **What a client of etcd can observe.** -/
structure State where
  kv : KVHist
  leases : Int → Option LeaseRec
  /-- every lease id ever granted, in order -/
  granted : List Int
  /-- the lease tables the cluster has had before the current one, in order (one per grant or
  revocation): what a member whose lessor is behind answers a lease read from -/
  leaseHist : List (Int → Option LeaseRec)
  auth : AuthState
  /-- the auth states the cluster has had before the current one, in order (one per change of the
  auth state, `AuthEnable` included): what a read's permission check may have seen -/
  authHist : List AuthState
  members : List Member
  alarms : List Alarm

/-- A new cluster with the members `ms`: revision `1`, nothing stored, no lease, auth off. -/
def State.init (ms : List Member) : State :=
  { kv := { revs := [], compacted := 0 }, leases := fun _ => none, granted := [], leaseHist := [], authHist := [],
    auth := { enabled := false, rev := 1, users := fun _ => none, roles := fun _ => none },
    members := ms, alarms := [] }

/-- **Every auth state the cluster has had**, the current one last. -/
def State.authTables (σ : State) : List AuthState := σ.authHist ++ [σ.auth]

/-- The keys attached to lease `id`: the keys whose record names it. -/
def State.attached (σ : State) (id : Int) (k : Key) : Prop :=
  ∃ r, σ.kv.store k = some r ∧ r.lease = id

/-! ## Errors -/

/-- **etcd's client-facing errors** (`rpctypes.Err*`, one each). -/
inductive EtcdErr where
  | emptyKey | keyNotFound | valueProvided | leaseProvided | tooManyOps | duplicateKey
  | invalidSortOption | compacted | futureRev | noSpace
  | leaseNotFound | leaseExist | leaseTTLTooLarge
  | memberExist | peerURLExist | memberNotEnoughStarted | memberBadURLs | memberNotFound
  | memberNotLearner | memberLearnerNotReady | tooManyLearners
  | requestTooLarge | tooManyRequests
  | rootUserNotExist | rootRoleNotExist | userAlreadyExist | userEmpty | userNotFound
  | roleAlreadyExist | roleNotFound | roleEmpty | authFailed | permissionDenied | roleNotGranted
  | permissionNotGranted | authNotEnabled | invalidAuthToken | authOldRevision | invalidAuthMgmt
  | clusterIdMismatch
  | noLeader | notLeader | leaderChanged | notCapable | stopped | timeout
  | timeoutDueToLeaderFail | timeoutDueToConnectionLost | timeoutWaitAppliedIndex | unhealthy
  | corrupt | badLeaderTransferee | clusterVersionUnavailable | wrongDowngradeVersionFormat
  | invalidDowngradeTargetVersion | downgradeInProcess | noInflightDowngrade
  | canceled | deadlineExceeded | notSupportedForLearner | invalidClientAPIVersion | watchCanceled
  | permissionNotGiven

/-- **The errors after which the request may still take effect** (or may have): the leader or
the connection lost, a timeout, a stopping or unhealthy server. A client learns nothing from one.
Every other `EtcdErr` is definite: the request was linearized (`Step`) with that answer. -/
def EtcdErr.indefinite : EtcdErr → Bool
  | .noLeader | .notLeader | .leaderChanged | .notCapable | .stopped | .timeout
  | .timeoutDueToLeaderFail | .timeoutDueToConnectionLost | .timeoutWaitAppliedIndex
  | .unhealthy | .clusterIdMismatch | .clusterVersionUnavailable | .badLeaderTransferee
  | .canceled | .deadlineExceeded | .watchCanceled
  -- an over-quota member applies a write and answers `ErrNoSpace`
  -- (`nonissues/etcd-apply-quota-nospace-after-write.md`)
  | .noSpace => true
  | _ => false

/-- **The refusals any request may meet**, the state unchanged: the server's admission control
(too many requests, a request too large, the quota or an alarm, a stale or bad token the client's
retries gave up on, a failed token refresh (`ErrAuthFailed`: the client's interceptor returns the
refresh's error for a request never applied), a learner refusing a request it does not serve, a
client version refused, a member not ready). -/
def EtcdErr.refusal : EtcdErr → Bool
  | .tooManyRequests | .requestTooLarge | .noSpace | .corrupt | .invalidAuthToken
  | .authOldRevision | .userEmpty | .authFailed | .notSupportedForLearner
  | .invalidClientAPIVersion | .memberNotEnoughStarted | .memberLearnerNotReady
  | .unhealthy => true
  | _ => false

/-! ## Requests -/

/-- `RangeRequest_SortOrder`: `NONE`, `ASCEND`, `DESCEND`. -/
def sortNone : Int := 0
def sortAscend : Int := 1
def sortDescend : Int := 2
/-- `RangeRequest_SortTarget`: `KEY`, `VERSION`, `CREATE`, `MOD`, `VALUE`. -/
def targetKey : Int := 0
def targetVersion : Int := 1
def targetCreate : Int := 2
def targetMod : Int := 3
def targetValue : Int := 4

/-- `etcdserverpb.RangeRequest`. -/
structure RangeReq where
  key : Key
  rangeEnd : Bytes
  limit : Int
  revision : Int
  sortOrder : Int
  sortTarget : Int
  serializable : Bool
  keysOnly : Bool
  countOnly : Bool
  minModRevision : Int
  maxModRevision : Int
  minCreateRevision : Int
  maxCreateRevision : Int

def RangeReq.range (r : RangeReq) : KeyRange := { key := r.key, rangeEnd := r.rangeEnd }

/-- `etcdserverpb.PutRequest`. -/
structure PutReq where
  key : Key
  value : Bytes
  lease : Int
  prevKv : Bool
  ignoreValue : Bool
  ignoreLease : Bool

/-- `etcdserverpb.DeleteRangeRequest`. -/
structure DeleteReq where
  key : Key
  rangeEnd : Bytes
  prevKv : Bool

def DeleteReq.range (d : DeleteReq) : KeyRange := { key := d.key, rangeEnd := d.rangeEnd }

/-- `Compare_CompareResult`: `EQUAL`, `GREATER`, `LESS`, `NOT_EQUAL`. -/
def cmpEqual : Int := 0
def cmpGreater : Int := 1
def cmpLess : Int := 2
def cmpNotEqual : Int := 3
/-- `Compare_CompareTarget`: `VERSION`, `CREATE`, `MOD`, `VALUE`, `LEASE`. -/
def cmpTVersion : Int := 0
def cmpTCreate : Int := 1
def cmpTMod : Int := 2
def cmpTValue : Int := 3
def cmpTLease : Int := 4

/-- `Compare`'s `target_union`: the value compared against, if set. -/
inductive CmpVal where
  | none
  | version (n : Int)
  | createRevision (n : Int)
  | modRevision (n : Int)
  | value (v : Bytes)
  | lease (n : Int)

/-- `etcdserverpb.Compare`. -/
structure Compare where
  result : Int
  target : Int
  key : Key
  rangeEnd : Bytes
  targetUnion : CmpVal

def Compare.range (c : Compare) : KeyRange := { key := c.key, rangeEnd := c.rangeEnd }

/-- `etcdserverpb.RequestOp` (and, in `txn`, a nested `TxnRequest`: its compares, success and
failure operations). -/
inductive RequestOp where
  | empty
  | range (r : RangeReq)
  | put (p : PutReq)
  | deleteRange (d : DeleteReq)
  | txn (compare : List Compare) (success failure : List RequestOp)

/-- `etcdserverpb.TxnRequest`. -/
structure TxnReq where
  compare : List Compare
  success : List RequestOp
  failure : List RequestOp

/-- **A request** to the cluster (the v3 RPCs a client's call becomes). -/
inductive Req where
  | range (r : RangeReq)
  | put (p : PutReq)
  | deleteRange (d : DeleteReq)
  | txn (t : TxnReq)
  /-- `Compact(revision, physical)` -/
  | compact (revision : Int) (physical : Bool)
  /-- `LeaseGrant(ID, TTL)`: `ID = 0` lets the server choose -/
  | leaseGrant (id : Int) (ttl : Int)
  | leaseRevoke (id : Int)
  /-- one keep-alive of `LeaseKeepAlive`'s stream -/
  | leaseKeepAlive (id : Int)
  | leaseTimeToLive (id : Int) (keys : Bool)
  | leaseLeases
  | authEnable
  | authDisable
  | authStatus
  | authenticate (name password : GoString)
  | userAdd (name : GoString) (password : GoString) (noPassword : Bool)
  | userGet (name : GoString)
  | userList
  | userDelete (name : GoString)
  | userChangePassword (name password : GoString)
  | userGrantRole (user role : GoString)
  | userRevokeRole (user role : GoString)
  | roleAdd (name : GoString)
  | roleGet (name : GoString)
  | roleList
  | roleDelete (name : GoString)
  | roleGrantPermission (name : GoString) (perm : Perm)
  | roleRevokePermission (role : GoString) (key rangeEnd : Bytes)
  | memberAdd (peerURLs : List GoString) (isLearner : Bool)
  | memberRemove (id : Nat)
  | memberUpdate (id : Nat) (peerURLs : List GoString)
  | memberPromote (id : Nat)
  /-- `linearizable`: the request's `Linearizable` flag -/
  | memberList (linearizable : Bool)
  /-- `Alarm(GET)`: the raised alarms -/
  | alarmList
  /-- `Alarm(DEACTIVATE, member, alarm)` -/
  | alarmDisarm (a : Alarm)
  /-- `Alarm(ACTIVATE, member, alarm)` -/
  | alarmActivate (a : Alarm)

/-! ## Answers -/

/-- `RangeResponse`'s contents (the header's revision apart). -/
structure RangeAns where
  kvs : List KV
  more : Bool
  count : Nat

/-- An operation's answer inside a transaction (`ResponseOp`). Only the nested ranges' header
revisions are modelled (the STM pins its later reads at them). -/
inductive OpResp where
  /-- a nested range: the revision of the transaction's view when it ran (one more after the
  transaction's first write: `storeTxnWrite.Range`), and its answer -/
  | range (rev : Nat) (a : RangeAns)
  | put (prev : Option KV)
  | deleteRange (deleted : Nat) (prevKvs : List KV)
  | txn (succeeded : Bool) (responses : List OpResp)
  | empty

/-- **A successful answer.** `rev` is the header's revision where etcd fixes it (the KV
operations); the other RPCs' headers are not modelled. -/
inductive RespBody where
  | range (rev : Nat) (a : RangeAns)
  | put (rev : Nat) (prev : Option KV)
  | deleteRange (rev : Nat) (deleted : Nat) (prevKvs : List KV)
  | txn (rev : Nat) (succeeded : Bool) (responses : List OpResp)
  | compact
  | leaseGrant (id : Int) (ttl : Int)
  | leaseRevoke
  | leaseKeepAlive (id : Int) (ttl : Int)
  /-- `ttl`: remaining seconds (`-1` once expired), `grantedTTL`, the attached keys if asked -/
  | leaseTimeToLive (id : Int) (ttl : Int) (grantedTTL : Int) (keys : List Key)
  | leaseLeases (ids : List Int)
  | authEnable
  | authDisable
  | authStatus (enabled : Bool) (authRev : Nat)
  /-- authenticated (the token the reply carries is not modelled: `State.lean`'s `tokenUser`) -/
  | authenticate
  | userAdd
  | userGet (roles : List GoString)
  | userList (users : List GoString)
  | userDelete
  | userChangePassword
  | userGrantRole
  | userRevokeRole
  | roleAdd
  | roleGet (perms : List Perm)
  | roleList (roles : List GoString)
  | roleDelete
  | roleGrantPermission
  | roleRevokePermission
  | memberAdd (m : Member) (members : List Member)
  | memberRemove (members : List Member)
  | memberUpdate (members : List Member)
  | memberPromote (members : List Member)
  | memberList (members : List Member)
  | alarm (alarms : List Alarm)

/-- **An answer**: success, or one of etcd's errors. -/
inductive Resp where
  | ok (b : RespBody)
  | err (e : EtcdErr)

/-! ## Range semantics -/

def RangeReq.validSort (r : RangeReq) : Prop :=
  (r.sortOrder = sortNone ∨ r.sortOrder = sortAscend ∨ r.sortOrder = sortDescend) ∧
  (r.sortTarget = targetKey ∨ r.sortTarget = targetVersion ∨ r.sortTarget = targetCreate ∨
    r.sortTarget = targetMod ∨ r.sortTarget = targetValue)

/-- `IsDefaultOrdering`. -/
def isDefaultOrdering (target order : Int) : Prop :=
  order = sortNone ∨ (target = targetKey ∧ order = sortAscend)

def RangeReq.hasRevFilters (r : RangeReq) : Prop :=
  r.minModRevision ≠ 0 ∨ r.maxModRevision ≠ 0 ∨ r.minCreateRevision ≠ 0 ∨
    r.maxCreateRevision ≠ 0

open Classical in
/-- `rangeLimit`: the limit mvcc is asked (`0`: none): one more than asked, unless an order or a
filter is set. **etcd's quirk** (`issues/etcd-range-sort-none-limit.md`): the order tested is the
request's, so a sort target other than the key with no order pushes the limit down before the
sort. -/
def RangeReq.pushdownLimit (r : RangeReq) : Nat :=
  if ¬ isDefaultOrdering r.sortTarget r.sortOrder ∨ r.hasRevFilters then 0
  else if 0 < r.limit then (r.limit + 1).toNat else 0

open Classical in
/-- The revision filters (`filterRangeResults`). -/
def RangeReq.keeps (r : RangeReq) (kv : KV) : Bool :=
  decide ((r.maxModRevision = 0 ∨ (kv.modRev : Int) ≤ r.maxModRevision) ∧
    (r.minModRevision = 0 ∨ r.minModRevision ≤ (kv.modRev : Int)) ∧
    (r.maxCreateRevision = 0 ∨ (kv.createRev : Int) ≤ r.maxCreateRevision) ∧
    (r.minCreateRevision = 0 ∨ r.minCreateRevision ≤ (kv.createRev : Int)))

/-- The strict order of a sort target. -/
def targetLt (target : Int) (a b : KV) : Prop :=
  if target = targetVersion then a.version < b.version
  else if target = targetCreate then a.createRev < b.createRev
  else if target = targetMod then a.modRev < b.modRev
  else if target = targetValue then keyLt a.value b.value
  else keyLt a.key b.key

open Classical in
/-- `sortRangeResults`: `out` is `l` sorted by the request's target and order (a target other than
the key with no order sorts ascending); left alone at the default ordering. Go's `sort.Sort` is not
stable: equal elements in any order. -/
def RangeReq.sorted (r : RangeReq) (l out : List KV) : Prop :=
  let order := if r.sortTarget ≠ targetKey ∧ r.sortOrder = sortNone then sortAscend else r.sortOrder
  if isDefaultOrdering r.sortTarget order then out = l
  else out.Perm l ∧
    (if order = sortDescend then out.Pairwise (fun a b => ¬ targetLt r.sortTarget a b)
     else out.Pairwise (fun a b => ¬ targetLt r.sortTarget b a))

/-- `FastKeysOnly`: a keys-only read not sorted by value is served from the index, and reports
lease `0` (**etcd's quirk**, `issues/etcd-range-keys-only-lease.md`). -/
def RangeReq.fastKeysOnly (r : RangeReq) : Prop := r.keysOnly = true ∧ r.sortTarget ≠ targetValue

open Classical in
/-- **A range's answer from the store `s`** (`executeRange`): the keys of the range in key order
(`all`), cut at the pushed-down limit, the revision filters, the sort, the request's limit
(`more` if it cut), values dropped for keys-only; `count` all the keys of the range. -/
def RangeReq.answers (r : RangeReq) (s : Store) (a : RangeAns) : Prop :=
  ∃ all : List KV, s.rangeKVs r.range all ∧
    if r.countOnly then a = { kvs := [], more := false, count := all.length }
    else
      let fetched := if r.pushdownLimit = 0 then all else all.take r.pushdownLimit
      let fetched := if r.fastKeysOnly then fetched.map (fun kv => { kv with lease := 0 })
        else fetched
      ∃ sorted, r.sorted (fetched.filter r.keeps) sorted ∧
        let cut := 0 < r.limit ∧ r.limit < sorted.length
        let out := if cut then sorted.take r.limit.toNat else sorted
        a = { kvs := if r.keysOnly then out.map (fun kv => { kv with value := [] }) else out,
              more := decide cut, count := all.length }

/-- The revision a range reads in the history `h`: the one asked, or the current. -/
def RangeReq.readRev (r : RangeReq) (h : KVHist) : Nat :=
  if r.revision ≤ 0 then h.rev else r.revision.toNat

/-- `checkRange` (and mvcc's own check): the error a range at the history `h` fails with. -/
def RangeReq.revErr (r : RangeReq) (h : KVHist) : Option EtcdErr :=
  if (h.rev : Int) < r.revision then some .futureRev
  else if 0 < r.revision ∧ r.revision < (h.compacted : Int) then some .compacted
  else none

/-- `checkRange` inside a transaction (`txn/range.go`): against the history's first revision,
which is `-1` before any compaction (`compactMainRev`), so a negative revision below it is
`ErrCompacted` there. -/
def RangeReq.txnRevErr (r : RangeReq) (h : KVHist) : Option EtcdErr :=
  if r.revision = 0 then none
  else if (h.rev : Int) < r.revision then some .futureRev
  else if r.revision < (if h.compacted = 0 then -1 else (h.compacted : Int)) then some .compacted
  else none

/-! ## Writes -/

/-- The record a put writes at revision `R` over the key's previous record `prev`. -/
def PutReq.record (p : PutReq) (R : Nat) (prev : Option KeyRec) : KeyRec :=
  { createRev := (prev.map (·.createRev)).getD R,
    modRev := R,
    version := (prev.map (·.version)).getD 0 + 1,
    value := if p.ignoreValue then (prev.map (·.value)).getD [] else p.value,
    lease := if p.ignoreLease then (prev.map (·.lease)).getD 0 else p.lease }

open Classical in
/-- `checkPut` at the store `s` and the live leases: the put's lease is live, and a key an ignore
flag needs exists. -/
def PutReq.check (p : PutReq) (s : Store) (leases : Int → Option LeaseRec) : Option EtcdErr :=
  if p.lease ≠ 0 ∧ leases p.lease = none then some .leaseNotFound
  else if (p.ignoreValue ∨ p.ignoreLease) ∧ s p.key = none then some .keyNotFound
  else none

/-- The gRPC layer's validation of a put (`checkPutRequest`). -/
def PutReq.invalid (p : PutReq) : Option EtcdErr :=
  if p.key = [] then some .emptyKey
  else if p.ignoreValue = true ∧ p.value ≠ [] then some .valueProvided
  else if p.ignoreLease = true ∧ p.lease ≠ 0 then some .leaseProvided
  else none

/-! ## Transactions -/

/-- `compareKV`: the comparison `c` holds of the key-value `kv`. -/
def Compare.holdsOf (c : Compare) (kv : KV) : Prop :=
  let res : Int :=
    if c.target = cmpTValue then
      let v := match c.targetUnion with | .value v => v | _ => []
      if keyLt kv.value v then -1 else if kv.value = v then 0 else 1
    else
      let n : Int :=
        if c.target = cmpTCreate then (kv.createRev : Int)
        else if c.target = cmpTMod then (kv.modRev : Int)
        else if c.target = cmpTVersion then (kv.version : Int)
        else if c.target = cmpTLease then kv.lease else 0
      let w : Int := match c.targetUnion with
        | .version n => if c.target = cmpTVersion then n else 0
        | .createRevision n => if c.target = cmpTCreate then n else 0
        | .modRevision n => if c.target = cmpTMod then n else 0
        | .lease n => if c.target = cmpTLease then n else 0
        | _ => 0
      if n < w then -1 else if n = w then 0 else 1
  if c.result = cmpEqual then res = 0
  else if c.result = cmpNotEqual then res ≠ 0
  else if c.result = cmpGreater then 0 < res
  else if c.result = cmpLess then res < 0
  else True

/-- The zero key-value a comparison of a missing key compares with. -/
def KV.zero (k : Key) : KV :=
  { key := k, createRev := 0, modRev := 0, version := 0, value := [], lease := 0 }

/-- `applyCompare` at the store `s`: over every key of the comparison's range; with no key, a
value comparison fails and the others compare the zero key-value. -/
def Compare.holds (c : Compare) (s : Store) : Prop :=
  ∃ l, s.rangeKVs c.range l ∧
    if l = [] then c.target ≠ cmpTValue ∧ c.holdsOf (KV.zero c.key) else ∀ kv ∈ l, c.holdsOf kv

/-- **A transaction's run** (`checkTxn`, `executeTxn`), as a relation from the pre-transaction store
`s0` (where the comparisons and the checks read), the live leases, the revision `R` its writes take,
the store `s` and events so far, to the store and events after `ops` with their answers, or the
check's error. Reads inside the transaction see its earlier writes. -/
inductive TxnRun (h : KVHist) (s0 : Store) (leases : Int → Option LeaseRec) (R : Nat) :
    List RequestOp → Store × List Event → Except EtcdErr (Store × List Event × List OpResp) → Prop
  | nil (st) : TxnRun h s0 leases R [] st (.ok (st.1, st.2, []))
  | empty (rest st res) : TxnRun h s0 leases R rest st res →
      TxnRun h s0 leases R (.empty :: rest) st
        (res.map (fun x => (x.1, x.2.1, .empty :: x.2.2)))
  | rangeErr (r : RangeReq) (rest st e) : r.txnRevErr h = some e →
      TxnRun h s0 leases R (.range r :: rest) st (.error e)
  | range (r : RangeReq) (rest st a res) : r.txnRevErr h = none →
      r.answers (if r.revision ≤ 0 then st.1 else h.storeAt r.revision.toNat) a →
      TxnRun h s0 leases R rest st res →
      TxnRun h s0 leases R (.range r :: rest) st
        (res.map (fun x => (x.1, x.2.1, .range (if st.2 = [] then h.rev else R) a :: x.2.2)))
  | putErr (p : PutReq) (rest st e) : p.check s0 leases = some e →
      TxnRun h s0 leases R (.put p :: rest) st (.error e)
  | put (p : PutReq) (rest st res) : p.check s0 leases = none →
      TxnRun h s0 leases R rest
        ((st.1.applyEvent (.put p.key (p.record R (st.1 p.key)))), st.2 ++ [.put p.key (p.record R (st.1 p.key))]) res →
      TxnRun h s0 leases R (.put p :: rest) st
        (res.map (fun x => (x.1, x.2.1,
          .put (if p.prevKv then (st.1 p.key).map (KV.ofRec p.key) else none) :: x.2.2)))
  | deleteRange (d : DeleteReq) (rest st) (l : List KV) (res) : st.1.rangeKVs d.range l →
      TxnRun h s0 leases R rest
        (st.1.applyEvents (l.map (fun kv => .delete kv.key)), st.2 ++ l.map (fun kv => .delete kv.key)) res →
      TxnRun h s0 leases R (.deleteRange d :: rest) st
        (res.map (fun x => (x.1, x.2.1,
          .deleteRange l.length (if d.prevKv then l else []) :: x.2.2)))
  | txnErr (cmps succ fail rest st e) :
      TxnRun h s0 leases R (if ∀ c ∈ cmps, c.holds s0 then succ else fail) st (.error e) →
      TxnRun h s0 leases R (.txn cmps succ fail :: rest) st (.error e)
  | txn (cmps succ fail rest st s' evs' rs res) :
      TxnRun h s0 leases R (if ∀ c ∈ cmps, c.holds s0 then succ else fail) st (.ok (s', evs', rs)) →
      TxnRun h s0 leases R rest (s', evs') res →
      TxnRun h s0 leases R (.txn cmps succ fail :: rest) st
        (res.map (fun x => (x.1, x.2.1, .txn (decide (∀ c ∈ cmps, c.holds s0)) rs :: x.2.2)))

-- **A transaction the gRPC layer accepts** (`checkTxnRequest`, `checkRequestOp`): every comparison
-- has a key, every operation of both branches, nested ones included, is valid (a range: a key and a
-- valid sort; a put: `checkPutRequest`; a delete: a key; no empty operation). Otherwise the
-- transaction is refused (`ErrEmptyKey`, `ErrValueProvided`, `ErrLeaseProvided`,
-- `ErrInvalidSortOption`, `ErrKeyNotFound`), never applied.
mutual
def RequestOp.valid : RequestOp → Prop
  | .empty => False
  | .range r => r.key ≠ [] ∧ r.validSort
  | .put p => p.invalid = none
  | .deleteRange d => d.key ≠ []
  | .txn cmps succ fail => (∀ c ∈ cmps, c.key ≠ []) ∧ RequestOp.validL succ ∧ RequestOp.validL fail
def RequestOp.validL : List RequestOp → Prop
  | [] => True
  | op :: ops => op.valid ∧ RequestOp.validL ops
end

def TxnReq.valid (t : TxnReq) : Prop := (RequestOp.txn t.compare t.success t.failure).valid

/-- **Each key put at most once in a transaction's events** (`putOnce`): the gRPC layer's
duplicate-key check (`api/v3rpc/key.go`, `checkIntervals`) refuses a transaction that puts one
key twice on a path (at any nesting level; a `Then` and an `Else` putting the same key are
alternatives) or puts a key a delete of its level or an enclosing one covers. A delete after a put
of the key in a later sibling nested transaction is accepted
(`issues/etcd-txn-check-intervals-sibling.md`), so the events may delete a key put earlier. -/
def putOnce (evs : List Event) : Prop :=
  ∀ k, (evs.filter (fun e => match e with
    | .put k' _ => decide (k' = k)
    | .delete _ => false)).length ≤ 1

/-- `IsTxnReadonly`: only ranges, in both branches (a nested transaction is a write). -/
def TxnReq.readonly (t : TxnReq) : Prop :=
  (∀ op ∈ t.success, ∃ r, op = .range r) ∧ (∀ op ∈ t.failure, ∃ r, op = .range r)

/-- `IsTxnSerializable`: only serializable ranges, in both branches (true of the empty
transaction). -/
def TxnReq.serializable (t : TxnReq) : Prop :=
  (∀ op ∈ t.success, ∃ r, op = .range r ∧ r.serializable = true) ∧
  (∀ op ∈ t.failure, ∃ r, op = .range r ∧ r.serializable = true)

/-- **A read** (`Req.isRead`): a range, or a read-only transaction. A client's update for a read
is persistent: the cluster may fire it at every state until a member reads, and a read may be
retried. -/
def Req.isRead : Req → Bool
  | .range _ => true
  | .txn t => decide t.readonly
  | _ => false

/-! ## Permissions -/

-- What a request reads and writes, for the permission check: `(type, range)` pairs. A
-- transaction checks its comparisons (read) and the operations of both branches, nested ones
-- included (`checkTxnAuth`); a `prevKv` also reads.
mutual
def RequestOp.perms : RequestOp → List (PermType × KeyRange)
  | .empty => []
  | .range r => [(.read, r.range)]
  | .put p => [(.write, { key := p.key, rangeEnd := [] })] ++
      (if p.prevKv then [(.read, { key := p.key, rangeEnd := [] })] else [])
  | .deleteRange d => [(.write, d.range)] ++ (if d.prevKv then [(.read, d.range)] else [])
  | .txn cmps succ fail => cmps.map (fun c => (.read, c.range)) ++ RequestOp.permsL succ ++
      RequestOp.permsL fail
def RequestOp.permsL : List RequestOp → List (PermType × KeyRange)
  | [] => []
  | op :: ops => op.perms ++ RequestOp.permsL ops
end

-- The leases a request's puts name (both branches of a transaction): a put naming a lease also
-- needs write permission on the keys already attached to it (`checkLeasePuts`).
mutual
def RequestOp.leases : RequestOp → List Int
  | .put p => if p.lease = 0 then [] else [p.lease]
  | .txn _ succ fail => RequestOp.leasesL succ ++ RequestOp.leasesL fail
  | _ => []
def RequestOp.leasesL : List RequestOp → List Int
  | [] => []
  | op :: ops => op.leases ++ RequestOp.leasesL ops
end

/-- **An administrator check refused, its two views** (`IsAdminPermitted`: the enabled flag read
at one auth table, the user at another; second pass, grpc-v3rpc's P-F5, the shape of 2a's
`V3rpc.adminDenied` and 3d's `adminPost`): the flag on at `jf`; no principal, or the empty user
(`ErrUserEmpty`), a user absent at `jx` (`ErrUserNotFound`), or present and not of the root role
(`ErrPermissionDenied`). -/
def State.adminDenied (σ : State) (who : Principal) (e : EtcdErr) : Prop :=
  ∃ (jf jx : Nat) (af ax : AuthState), σ.authTables[jf]? = some af ∧ σ.authTables[jx]? = some ax ∧
    af.enabled = true ∧
    match who with
    | none => e = .userEmpty
    | some u => (u = [] ∧ e = .userEmpty) ∨ (u ≠ [] ∧ ax.users u = none ∧ e = .userNotFound) ∨
        (u ≠ [] ∧ ax.users u ≠ none ∧ ¬ ax.isRoot u ∧ e = .permissionDenied)

/-- An administrator's request (`IsAdminPermitted`): auth off or a user of the root role. -/
def AuthState.admin (a : AuthState) (who : Principal) : Prop :=
  a.enabled = false ∨ ∃ u, who = some u ∧ a.isRoot u

/-- **The permission check** (`isOpPermitted`, `checkLeasePuts`) of a request reading and writing
`ps` and putting keys on the leases `ls`, at the state `σ`: auth off, or the principal a user of
the root role, or each pair and each key attached to those leases covered by the principal's roles
(checked one by one: with nothing to check, no principal is needed). -/
def State.permits (σ : State) (who : Principal) (ps : List (PermType × KeyRange))
    (ls : List Int) : Prop :=
  σ.auth.enabled = false ∨ (∃ u, who = some u ∧ σ.auth.isRoot u) ∨
    ((∀ p ∈ ps, ∃ u, who = some u ∧ σ.auth.covers u p.1 p.2) ∧
     ∀ l ∈ ls, ∀ k, (∃ r, σ.kv.store k = some r ∧ r.lease = l) →
       ∃ u, who = some u ∧ σ.auth.covers u .write { key := k, rangeEnd := [] })

/-- **A read checked at an auth state with auth off, since the auth state `lo`** (`doSerialize`:
with auth off at the check, `AuthInfoFromCtx` gives no credentials, the check passes and no
revision is re-checked after the read, so a read whose check saw auth off is answered whatever the
auth state at the answer: `nonissues/etcd-doserialize-auth-enable-race.md`). `lo` is the index of
the auth state when the call started (`authLb`). -/
def State.authOffSince (σ : State) (lo : Nat) : Prop :=
  ∃ j a, lo ≤ j ∧ σ.authTables[j]? = some a ∧ a.enabled = false

/-- **A read permitted at an auth state since `lo`** (`doSerialize`'s check at the member's auth
state, which may be older than the answer's: auth off at the check, `authOffSince`, the round-4
race; or an auth change applied but not yet published to readers, its revision already bumped
(`auth/store.go`: `commitRevision` before the batch's unlock), so the post-read revision check
passes: 3d's review F4). Subsumes `authOffSince`. -/
def State.permittedSince (σ : State) (lo : Nat) (who : Principal) (ps : List (PermType × KeyRange)) :
    Prop :=
  ∃ j a, lo ≤ j ∧ σ.authTables[j]? = some a ∧ ({ σ with auth := a } : State).permits who ps []

/-- **A read denied, its check's three views since `lo`** (`isOpPermitted`, one call per pair:
it reads the enabled flag, then the user under the backend's read transaction, then the permission
cache, each at an auth state it saw, which may differ and be older than the answer's: 3d's
`checkDenied`): for one pair, auth on at one table, and either no principal (`ErrUserEmpty`) or a
user not of the root role at a second table whose range is not covered (or inverted) at a third.
Verify round, A9-completeness F1: it was the denial at one auth state, which the code does not give
(an `AuthDisable` and a `RoleRevokePermission` between the views deny a read permitted at every
state; `nonissues/etcd-auth-read-denied-across-views.md`). A denial at one state is the case
`jf = jx = jc`. -/
def State.deniedSince (σ : State) (lo : Nat) (who : Principal) (ps : List (PermType × KeyRange)) :
    Prop :=
  ∃ p ∈ ps, ∃ (jf jx jc : Nat) (af ax ac : AuthState), lo ≤ jf ∧ lo ≤ jx ∧ lo ≤ jc ∧
    σ.authTables[jf]? = some af ∧ σ.authTables[jx]? = some ax ∧ σ.authTables[jc]? = some ac ∧
    af.enabled = true ∧
    (who = none ∨ ∃ u, who = some u ∧ ¬ ax.isRoot u ∧ (¬ ac.covers u p.1 p.2 ∨ p.2.inverted))

/-- **A denial of an inverted range** (`auth/range_perm_cache.go`: the interval tree's `Contains`
of an empty interval may refuse it): auth on, a principal not of the root role, and a pair whose
range is inverted. -/
def State.invertedDeny (σ : State) (who : Principal) (ps : List (PermType × KeyRange)) : Prop :=
  σ.auth.enabled = true ∧ ¬ (∃ u, who = some u ∧ σ.auth.isRoot u) ∧ ∃ p ∈ ps, p.2.inverted

/-- The error of a failed permission check: no principal (`ErrUserEmpty`), or a denial. -/
def AuthState.permErr (who : Principal) : EtcdErr :=
  match who with
  | none => .userEmpty
  | some _ => .permissionDenied

/-- The error of a failed administrator check: no principal, no such user, or a denial. -/
def AuthState.adminErr (a : AuthState) (who : Principal) : EtcdErr :=
  match who with
  | none => .userEmpty
  | some u => if a.users u = none then .userNotFound else .permissionDenied

/-! ## The steps -/

/-- The KV part of a state replaced. -/
def State.withKV (σ : State) (h : KVHist) : State := { σ with kv := h }

/-- A lease revoked: its keys deleted at one new revision (in key order), the lease gone. -/
def State.revoke (σ : State) (id : Int) (l : List KV) : State :=
  { σ with kv := σ.kv.commit (l.map (fun kv => .delete kv.key)),
           leases := fun i => if i = id then none else σ.leases i,
           leaseHist := σ.leaseHist ++ [σ.leases] }

/-- **Every lease table the cluster has had**, the current one last: table `i` is the live leases
after the `i`-th grant or revocation. A member's lessor reflects one of them, and a member's
lessor only moves forward (`State.lean`'s `leaseViewLb`, per member). -/
def State.leaseTables (σ : State) : List (Int → Option LeaseRec) := σ.leaseHist ++ [σ.leases]

/-- **A lease read answered from lease table `i`** (`LeaseLeases`: exactly the live ids, no
duplicates, any order; `LeaseTimeToLive` of a live lease, or `ErrLeaseNotFound` of one that is not:
the lessor of the member answering, `v3_server.go`, which may be behind). -/
def State.leaseAnsAt (σ : State) (i : Nat) (rq : Req) (res : Resp) : Prop :=
  ∃ t, σ.leaseTables[i]? = some t ∧
  match rq, res with
  | .leaseLeases, .ok (.leaseLeases ids) => ids.Nodup ∧ ∀ x, x ∈ ids ↔ t x ≠ none
  | .leaseTimeToLive id _, .ok (.leaseTimeToLive id' _ _ _) => id' = id ∧ t id ≠ none
  | .leaseTimeToLive id _, .err .leaseNotFound => t id = none
  | _, _ => False

/-- `l`: the keys attached to `id`, sorted. -/
def State.attachedKVs (σ : State) (id : Int) (l : List KV) : Prop :=
  l.Pairwise (fun a b => keyLt a.key b.key) ∧
  ∀ kv, kv ∈ l ↔ (kv.lease = id ∧ σ.kv.store kv.key = some
    { createRev := kv.createRev, modRev := kv.modRev, version := kv.version, value := kv.value,
      lease := kv.lease })

/-- The KV steps (the success and the deterministic errors of `Range`, `Put`, `DeleteRange`,
`Txn`, `Compact`), in the order etcd checks: the gRPC layer's validation, the permission check,
then the operation's own checks. -/
def kvStep (who : Principal) (rq : Req) (σ σ' : State) (res : Resp) (lo : Nat := 0) : Prop :=
  match rq with
  | .range r =>
      σ' = σ ∧
      (r.key = [] ∧ res = .err .emptyKey ∨
       ¬ r.validSort ∧ res = .err .invalidSortOption ∨  -- the client checks the sort first
       r.key ≠ [] ∧ r.validSort ∧
       -- a linearizable read is answered at the current history, a serializable one at the view
       -- of a member that may be behind (its permission check too, at an auth state not kept:
       -- a refusal it may make is `permErr`). A linearizable read's permission is checked at the
       -- state it answers from: `nonissues/etcd-doserialize-auth-enable-race.md` (a race with
       -- `AuthEnable` breaks it; a fix or a premise, open)
       ∃ v, (if r.serializable then σ.kv.IsView v else v = σ.kv) ∧
         ((¬ σ.permits who [(.read, r.range)] [] ∨ r.serializable = true ∨
             σ.invertedDeny who [(.read, r.range)] ∨
             σ.deniedSince lo who [(.read, r.range)]) ∧
            res = .err (AuthState.permErr who) ∨
          (σ.permits who [(.read, r.range)] [] ∨ r.serializable = true ∨
            σ.permittedSince lo who [(.read, r.range)]) ∧
          ((∃ e, r.revErr v = some e ∧ res = .err e) ∨
           r.revErr v = none ∧ ∃ a, r.answers (v.storeAt (r.readRev v)) a ∧
             res = .ok (.range v.rev a))))
  | .put p =>
      (∃ e, p.invalid = some e ∧ σ' = σ ∧ res = .err e) ∨
      p.invalid = none ∧
      (¬ σ.permits who (RequestOp.put p).perms (RequestOp.put p).leases ∧ σ' = σ ∧
          res = .err (AuthState.permErr who) ∨
       σ.permits who (RequestOp.put p).perms (RequestOp.put p).leases ∧
       ((∃ e, p.check σ.kv.store σ.leases = some e ∧ σ' = σ ∧ res = .err e) ∨
        p.check σ.kv.store σ.leases = none ∧
          σ' = σ.withKV (σ.kv.commit [.put p.key (p.record (σ.kv.rev + 1) (σ.kv.store p.key))]) ∧
          res = .ok (.put (σ.kv.rev + 1)
            (if p.prevKv then (σ.kv.store p.key).map (KV.ofRec p.key) else none))))
  | .deleteRange d =>
      (d.key = [] ∧ σ' = σ ∧ res = .err .emptyKey) ∨
      d.key ≠ [] ∧
      ((¬ σ.permits who (RequestOp.deleteRange d).perms [] ∨
          σ.invertedDeny who (RequestOp.deleteRange d).perms) ∧ σ' = σ ∧
          res = .err (AuthState.permErr who) ∨
       σ.permits who (RequestOp.deleteRange d).perms [] ∧
       ∃ l, σ.kv.store.rangeKVs d.range l ∧
         σ' = σ.withKV (σ.kv.commit (l.map (fun kv => .delete kv.key))) ∧
         res = .ok (.deleteRange σ'.kv.rev l.length (if d.prevKv then l else [])))
  | .txn t =>
      -- the gRPC layer's per-level checks refuse (too many operations, a key written twice,
      -- an operation's own validation)
      -- (an empty `RequestOp` is `ErrKeyNotFound` there: `checkRequestOp`'s default)
      (σ' = σ ∧ (res = .err .tooManyOps ∨ res = .err .duplicateKey ∨ res = .err .emptyKey ∨
        res = .err .valueProvided ∨ res = .err .leaseProvided ∨ res = .err .invalidSortOption ∨
        res = .err .keyNotFound)) ∨
      -- a read-only serializable transaction is checked at the answering member's auth state,
      -- which may be behind
      ((¬ σ.permits who (RequestOp.txn t.compare t.success t.failure).perms
          (RequestOp.txn t.compare t.success t.failure).leases ∨ (t.readonly ∧ t.serializable) ∨
          (t.readonly ∧ σ.deniedSince lo who (RequestOp.txn t.compare t.success t.failure).perms) ∨
          σ.invertedDeny who (RequestOp.txn t.compare t.success t.failure).perms) ∧
          σ' = σ ∧ res = .err (AuthState.permErr who)) ∨
      t.valid ∧
      (σ.permits who (RequestOp.txn t.compare t.success t.failure).perms
          (RequestOp.txn t.compare t.success t.failure).leases ∨ (t.readonly ∧ t.serializable) ∨
          (t.readonly ∧ σ.permittedSince lo who (RequestOp.txn t.compare t.success t.failure).perms)) ∧
      -- a read-only serializable transaction (the empty one included) is answered at the view
      -- of a member that may be behind (`issues/etcd-txn-empty-serializable.md`)
      ∃ v, (if t.readonly ∧ t.serializable then σ.kv.IsView v else v = σ.kv) ∧
        let s0 := v.store
        let ok := decide (∀ c ∈ t.compare, c.holds s0)
        let ops := if ok then t.success else t.failure
        ((∃ e, TxnRun v s0 σ.leases (v.rev + 1) ops (s0, []) (.error e) ∧ σ' = σ ∧ res = .err e) ∨
         ∃ s' evs rs, TxnRun v s0 σ.leases (v.rev + 1) ops (s0, []) (.ok (s', evs, rs)) ∧
           putOnce evs ∧
           σ' = σ.withKV (σ.kv.commit evs) ∧
           res = .ok (.txn (if evs = [] then v.rev else v.rev + 1) ok rs))
  | .compact rev _ =>
      -- the gRPC layer's administrator check, at the member's local auth tables (ones the
      -- cluster has had: `kvServer.Compact`), the flag and the user read at two moments
      (∃ e, σ.adminDenied who e ∧ σ' = σ ∧ res = .err e) ∨
      rev ≤ (σ.kv.compacted : Int) ∧ σ' = σ ∧ res = .err .compacted ∨
      (σ.kv.rev : Int) < rev ∧ σ' = σ ∧ res = .err .futureRev ∨
      (σ.kv.compacted : Int) < rev ∧ rev ≤ (σ.kv.rev : Int) ∧
        (∃ j a, lo ≤ j ∧ σ.authTables[j]? = some a ∧ a.admin who) ∧
        σ' = σ.withKV { σ.kv with compacted := rev.toNat } ∧ res = .ok .compact
  | _ => False

/-- `MaxLeaseTTL`. -/
def maxLeaseTTL : Int := 9000000000

/-- The lease steps. A grant's id is the one asked, or (`0`) one the server chose: it may be live
already (`ErrLeaseExist`, `issues/etcd-lease-id-mask-member-prefix.md`); the TTL granted is at
least the one asked (each member raises it to its own minimum). A keep-alive changes nothing and
is answered by the leader's lessor, which may be a deposed leader's: it tells nothing of the
lease's liveness. `TimeToLive` and `Leases` are answered from a lessor that may be behind or
deposed: a lease granted at some point, and keys attached to it at some revision. Their permission
errors are allowed at any state, auth off included (etcd checks them only with auth on, at the
answering member's possibly stale auth state, which the model does not keep). -/
def leaseStep (who : Principal) (rq : Req) (σ σ' : State) (res : Resp) : Prop :=
  match rq with
  | .leaseGrant id ttl =>
      σ' = σ ∧ maxLeaseTTL < ttl ∧ res = .err .leaseTTLTooLarge ∨
      ttl ≤ maxLeaseTTL ∧
        (σ' = σ ∧ (id = 0 ∨ σ.leases id ≠ none) ∧ res = .err .leaseExist ∨
         -- a chosen id is a positive int64 (`reqIDGen.Next()` masked to 63 bits); the TTL is the asked
         -- one raised to the member's minimum (`lessor.Grant`): positive, at most `MaxLeaseTTL`
         ∃ id' ttl', (id ≠ 0 → id' = id) ∧ id' ≠ 0 ∧ (id = 0 → 0 < id') ∧ -2 ^ 63 ≤ id' ∧ id' < 2 ^ 63 ∧
           σ.leases id' = none ∧ ttl ≤ ttl' ∧ 0 < ttl' ∧ ttl' ≤ maxLeaseTTL ∧
           σ' = { σ with leases := fun i => if i = id' then some { ttl := ttl' } else σ.leases i,
                         granted := σ.granted ++ [id'], leaseHist := σ.leaseHist ++ [σ.leases] } ∧
           res = .ok (.leaseGrant id' ttl'))
  | .leaseRevoke id =>
      σ.leases id = none ∧ σ' = σ ∧ res = .err .leaseNotFound ∨
      ∃ l, σ.leases id ≠ none ∧ σ.attachedKVs id l ∧
        (σ.permits who [] [id] ∧ σ' = σ.revoke id l ∧ res = .ok .leaseRevoke ∨
         ¬ σ.permits who [] [id] ∧ σ' = σ ∧ res = .err (AuthState.permErr who))
  | .leaseKeepAlive id =>
      -- `checkLeaseRenew`'s permission error, at a member's auth state
      σ' = σ ∧ (res = .err .leaseNotFound ∨ res = .err (AuthState.permErr who) ∨ ∃ ttl, -2 ^ 63 ≤ ttl ∧ ttl < 2 ^ 63 ∧ res = .ok (.leaseKeepAlive id ttl))
  | .leaseTimeToLive id keys =>
      σ' = σ ∧
      -- answered from the lease table `i` of the (leader's) lessor, which may be behind
      ((∃ i, σ.leaseAnsAt i (.leaseTimeToLive id keys) res) ∧
       (res = .err .leaseNotFound ∨
        -- the remaining TTL may exceed the granted one after a leader change (`Promote` extends)
        -- the granted TTL of a known lease is positive (`v3_server.go`, `LeaseTimeToLive`)
        ∃ ttl gttl r l, r ≤ σ.kv.rev ∧ -2 ^ 63 ≤ ttl ∧ ttl < 2 ^ 63 ∧ 0 < gttl ∧ gttl < 2 ^ 63 ∧
          -- keys attached at revision `r` or `r + 1` (the lessor's set may be half updated by an
          -- entry's writes, or half restored after a snapshot: `nonissues/etcd-lease-keys-mid-apply.md`)
          (∀ k ∈ l, ∃ rec, (σ.kv.storeAt r k = some rec ∨ σ.kv.storeAt (r + 1) k = some rec) ∧
            rec.lease = id) ∧
          res = .ok (.leaseTimeToLive id ttl gttl (if keys then l else []))) ∨
       -- the attached keys' read permission, checked at a member's auth state
       (keys = true ∧ res = .err (AuthState.permErr who)))
  | .leaseLeases =>
      σ' = σ ∧ (res = .err (AuthState.permErr who) ∨
        -- the live leases of the lease table `i` of the answering member's lessor
        ∃ i ids, σ.leaseAnsAt i .leaseLeases res ∧ res = .ok (.leaseLeases ids))
  | _ => False

/-- User `name`'s record replaced. -/
def AuthState.setUser (a : AuthState) (name : GoString) (ur : Option UserRec) : AuthState :=
  { a with users := fun u => if u = name then ur else a.users u }

/-- Role `name`'s permissions replaced. -/
def AuthState.setRole (a : AuthState) (name : GoString) (ps : Option (List Perm)) : AuthState :=
  { a with roles := fun r => if r = name then ps else a.roles r }

/-- `ps` without the permissions of exactly the range `key`, `rangeEnd`. -/
def Perm.dropRange (ps : List Perm) (key rangeEnd : Bytes) : List Perm :=
  ps.filter (fun q => ¬ (q.range.key = key ∧ q.range.rangeEnd = rangeEnd))

/-- Role `name` revoked from every user. -/
def AuthState.dropRole (a : AuthState) (name : GoString) : AuthState :=
  { a with users := fun u => Option.map (fun ur => { ur with roles := ur.roles.filter (· ≠ name) }) (a.users u) }

/-- **Who may call an auth RPC** (`needAdminPermission`, `authApplierV3.UserGet`/`RoleGet`): an
administrator; a user may also read its own record and the roles it has. -/
def AuthState.mayCall (a : AuthState) (who : Principal) (rq : Req) : Prop :=
  a.admin who ∨
  match rq with
  | .userGet n => who = some n ∨ (who = none ∧ n = [])  -- `""` matches no user's name
  | .roleGet r => ∃ u ur, who = some u ∧ a.users u = some ur ∧ r ∈ ur.roles
  | _ => False

/-- The auth RPCs that need an administrator (or the caller's own record, `mayCall`). -/
def Req.isAuthAdmin : Req → Prop
  | .authEnable | .authDisable | .userAdd .. | .userGet _ | .userList | .userDelete _
  | .userChangePassword .. | .userGrantRole .. | .userRevokeRole .. | .roleAdd _ | .roleGet _
  | .roleList | .roleDelete _ | .roleGrantPermission .. | .roleRevokePermission .. => True
  | _ => False

open Classical in
/-- The auth steps (`server/auth/store.go`). Every change bumps the auth revision; the changes and
the user and role reads need an administrator (a user may read its own record). -/
def authStep (who : Principal) (rq : Req) (σ σ' : State) (res : Resp) (lo : Nat := 0) : Prop :=
  let a := σ.auth
  let bump (a' : AuthState) : State :=
    { σ with auth := { a' with rev := a.rev + 1 }, authHist := σ.authHist ++ [σ.auth] }
  match rq with
  | .authenticate name pw =>
      σ' = σ ∧
      (a.enabled = false ∧ res = .err .authNotEnabled ∨
       a.enabled = true ∧
         ((∃ ur c, a.users name = some ur ∧ ur.password = some c ∧ pwMatch c pw) ∧
            res = .ok .authenticate ∨
          ¬ (∃ ur c, a.users name = some ur ∧ ur.password = some c ∧ pwMatch c pw) ∧
            res = .err .authFailed) ∨
       -- `CheckPassword`'s answers before proposing, at the member's auth state since `lo`
       (∃ j b, lo ≤ j ∧ σ.authTables[j]? = some b ∧
          (b.enabled = false ∧ res = .err .authNotEnabled ∨
           ¬ (∃ ur c, b.users name = some ur ∧ ur.password = some c ∧ pwMatch c pw) ∧
             res = .err .authFailed)))
  | .authStatus => σ' = σ ∧ res = .ok (.authStatus a.enabled a.rev)
  | _ =>
    rq.isAuthAdmin ∧
    (¬ a.mayCall who rq ∧ σ' = σ ∧ res = .err (a.adminErr who) ∨
    a.mayCall who rq ∧
    match rq with
    | .authEnable =>
        a.enabled = true ∧ σ' = σ ∧ res = .ok .authEnable ∨
        a.enabled = false ∧
          (a.users rootUser = none ∧ σ' = σ ∧ res = .err .rootUserNotExist ∨
           ¬ a.isRoot rootUser ∧ a.users rootUser ≠ none ∧ σ' = σ ∧ res = .err .rootRoleNotExist ∨
           -- `AuthEnable` keeps the auth revision (`setRevision` of the stored one)
           a.isRoot rootUser ∧
             σ' = { σ with auth := { a with enabled := true }, authHist := σ.authHist ++ [σ.auth] } ∧
             res = .ok .authEnable)
    | .authDisable =>
        σ' = (if a.enabled then (bump { a with enabled := false }) else σ) ∧ res = .ok .authDisable
    | .userAdd name pw noPw =>
        name = [] ∧ σ' = σ ∧ res = .err .userEmpty ∨
        name ≠ [] ∧ a.users name ≠ none ∧ σ' = σ ∧ res = .err .userAlreadyExist ∨
        name ≠ [] ∧ a.users name = none ∧ ∃ cred, (noPw = false → pwHash pw cred) ∧
          σ' = bump (a.setUser name (some ⟨if noPw then none else some cred, []⟩)) ∧
          res = .ok .userAdd
    | .userDelete name =>
        a.enabled = true ∧ name = rootUser ∧ σ' = σ ∧ res = .err .invalidAuthMgmt ∨
        ¬ (a.enabled = true ∧ name = rootUser) ∧
          (a.users name = none ∧ σ' = σ ∧ res = .err .userNotFound ∨
           a.users name ≠ none ∧
             σ' = bump (a.setUser name none) ∧
             res = .ok .userDelete)
    | .userChangePassword name pw =>
        a.users name = none ∧ σ' = σ ∧ res = .err .userNotFound ∨
        ∃ ur, a.users name = some ur ∧
          -- a password-less user stays password-less (`store.go`, `UserChangePassword`)
          ∃ cred, pwHash pw cred ∧
          σ' = bump (a.setUser name (some { ur with password := ur.password.map (fun _ => cred) })) ∧
          res = .ok .userChangePassword
    | .userGrantRole user role =>
        a.users user = none ∧ σ' = σ ∧ res = .err .userNotFound ∨
        a.users user ≠ none ∧ role ≠ rootRole ∧ a.roles role = none ∧ σ' = σ ∧ res = .err .roleNotFound ∨
        ∃ ur, a.users user = some ur ∧ (role = rootRole ∨ a.roles role ≠ none) ∧
          (role ∈ ur.roles ∧ σ' = σ ∨
           role ∉ ur.roles ∧ σ' = bump (a.setUser user (some { ur with roles := ur.roles ++ [role] }))) ∧
          res = .ok .userGrantRole
    | .userRevokeRole user role =>
        a.enabled = true ∧ user = rootUser ∧ role = rootRole ∧ σ' = σ ∧ res = .err .invalidAuthMgmt ∨
        a.users user = none ∧ σ' = σ ∧ res = .err .userNotFound ∨
        ∃ ur, a.users user = some ur ∧
          (role ∉ ur.roles ∧ σ' = σ ∧ res = .err .roleNotGranted ∨
           role ∈ ur.roles ∧
             σ' = bump (a.setUser user (some { ur with roles := ur.roles.filter (· ≠ role) })) ∧
           res = .ok .userRevokeRole)
    | .userGet name =>
        σ' = σ ∧ (a.users name = none ∧ res = .err .userNotFound ∨
          ∃ ur l, a.users name = some ur ∧ l.Perm ur.roles ∧ res = .ok (.userGet l))
    | .userList =>
        σ' = σ ∧ ∃ l, (∀ u, u ∈ l ↔ a.users u ≠ none) ∧ res = .ok (.userList l)
    | .roleAdd name =>
        name = [] ∧ σ' = σ ∧ res = .err .roleEmpty ∨
        name ≠ [] ∧ a.roles name ≠ none ∧ σ' = σ ∧ res = .err .roleAlreadyExist ∨
        name ≠ [] ∧ a.roles name = none ∧
          σ' = bump (a.setRole name (some [])) ∧
          res = .ok .roleAdd
    | .roleDelete name =>
        a.enabled = true ∧ name = rootRole ∧ σ' = σ ∧ res = .err .invalidAuthMgmt ∨
        ¬ (a.enabled = true ∧ name = rootRole) ∧
          (a.roles name = none ∧ σ' = σ ∧ res = .err .roleNotFound ∨
           a.roles name ≠ none ∧
             σ' = bump (AuthState.dropRole (a.setRole name none) name) ∧
             res = .ok .roleDelete)
    | .roleGrantPermission name perm =>
        -- an invalid range or a missing permission (`store.go`, `RoleGrantPermission`)
        σ' = σ ∧ (res = .err .invalidAuthMgmt ∨ res = .err .permissionNotGiven) ∨
        a.roles name = none ∧ σ' = σ ∧ res = .err .roleNotFound ∨
        ∃ ps, a.roles name = some ps ∧ perm.range.validPerm ∧
          σ' = bump (a.setRole name
            (some (Perm.dropRange ps perm.range.key perm.range.rangeEnd ++ [perm]))) ∧
          res = .ok .roleGrantPermission
    | .roleRevokePermission role key rangeEnd =>
        a.roles role = none ∧ σ' = σ ∧ res = .err .roleNotFound ∨
        ∃ ps, a.roles role = some ps ∧
          ((¬ ∃ q ∈ ps, q.range.key = key ∧ q.range.rangeEnd = rangeEnd) ∧ σ' = σ ∧
             res = .err .permissionNotGranted ∨
           (∃ q ∈ ps, q.range.key = key ∧ q.range.rangeEnd = rangeEnd) ∧
             σ' = bump (a.setRole role (some (Perm.dropRange ps key rangeEnd))) ∧
             res = .ok .roleRevokePermission)
    | .roleGet name =>
        σ' = σ ∧ (a.roles name = none ∧ res = .err .roleNotFound ∨
          -- a stored root role answers its fixed permission (`rootPerm`)
          name = rootRole ∧ a.roles name ≠ none ∧ (∃ ps, res = .ok (.roleGet ps)) ∨
          ∃ ps l, name ≠ rootRole ∧ a.roles name = some ps ∧ l.Perm ps ∧ res = .ok (.roleGet l))
    | .roleList =>
        σ' = σ ∧ ∃ l, (∀ r, r ∈ l ↔ a.roles r ≠ none) ∧ res = .ok (.roleList l)
    | _ => False)

/-- The membership and alarm steps (`server/etcdserver/api/membership`, `server.go`'s
`AddMember`, ...). A new member's id is the server's choice; lists come in any order (members
sorted by id, alarms from a map); `MemberList` with `linearizable` false is answered from a
member's possibly stale view (any list). The administrator check of these requests is made at the
member's local auth state before proposing, which may be behind: a refusal at any state, and the
change itself not conditioned on `σ`'s administrators. -/
def clusterStep (who : Principal) (rq : Req) (σ σ' : State) (res : Resp) : Prop :=
  match rq with
  | .memberAdd urls learner =>
      (σ' = σ ∧ res = .err (σ.auth.adminErr who)) ∨
      ((∃ m ∈ σ.members, ∃ u ∈ urls, u ∈ m.peerURLs) ∧ σ' = σ ∧ res = .err .peerURLExist ∨
       learner = true ∧ σ' = σ ∧ res = .err .tooManyLearners ∨
       -- unparsable URLs; an id the server chose that is (or was) a member's
       σ' = σ ∧ (res = .err .memberBadURLs ∨ res = .err .memberExist ∨ res = .err .memberNotFound) ∨
       ∃ id l, (∀ m ∈ σ.members, m.id ≠ id) ∧ id < 2 ^ 64 ∧
         let m : Member := { id := id, name := [], peerURLs := urls, clientURLs := [],
                             isLearner := learner }
         σ' = { σ with members := σ.members ++ [m] } ∧ l.Perm σ'.members ∧
         res = .ok (.memberAdd m l))
  | .memberRemove id =>
      (σ' = σ ∧ res = .err (σ.auth.adminErr who)) ∨
      ((∀ m ∈ σ.members, m.id ≠ id) ∧ σ' = σ ∧ res = .err .memberNotFound ∨
       (∃ m ∈ σ.members, m.id = id) ∧ σ' = { σ with members := σ.members.filter (·.id ≠ id) } ∧
         ∃ l, l.Perm σ'.members ∧ res = .ok (.memberRemove l))
  | .memberUpdate id urls =>
      (σ' = σ ∧ res = .err (σ.auth.adminErr who)) ∨
      ((∀ m ∈ σ.members, m.id ≠ id) ∧ σ' = σ ∧ res = .err .memberNotFound ∨
       (∃ m ∈ σ.members, m.id ≠ id ∧ ∃ u ∈ urls, u ∈ m.peerURLs) ∧ σ' = σ ∧
         res = .err .peerURLExist ∨
       (∃ m ∈ σ.members, m.id = id) ∧
         σ' = { σ with members := σ.members.map (fun m => if m.id = id then { m with peerURLs := urls } else m) } ∧
         ∃ l, l.Perm σ'.members ∧ res = .ok (.memberUpdate l))
  | .memberPromote id =>
      (σ' = σ ∧ res = .err (σ.auth.adminErr who)) ∨
      ((∀ m ∈ σ.members, m.id ≠ id) ∧ σ' = σ ∧ res = .err .memberNotFound ∨
       (∃ m ∈ σ.members, m.id = id ∧ m.isLearner = false) ∧ σ' = σ ∧
         res = .err .memberNotLearner ∨
       (∃ m ∈ σ.members, m.id = id ∧ m.isLearner = true) ∧
         σ' = { σ with members := σ.members.map (fun m => if m.id = id then { m with isLearner := false } else m) } ∧
         ∃ l, l.Perm σ'.members ∧ res = .ok (.memberPromote l))
  | .memberList lin =>
      σ' = σ ∧ (lin = true → ∃ l, l.Perm σ.members ∧ res = .ok (.memberList l)) ∧
        (lin = false → ∃ ms, res = .ok (.memberList ms))
  | .alarmList => σ' = σ ∧ ∃ l, l.Perm σ.alarms ∧ res = .ok (.alarm l)
  | .alarmActivate al =>
      (σ' = σ ∧ res = .err (σ.auth.adminErr who)) ∨
      al.memberId < 2 ^ 64 ∧
        ((∃ b ∈ σ.alarms, b.memberId = al.memberId ∧ b.kind = al.kind) ∧ σ' = σ ∨
         σ' = { σ with alarms := σ.alarms ++ [al] }) ∧ res = .ok (.alarm [al])
  | .alarmDisarm al =>
      (σ' = σ ∧ res = .err (σ.auth.adminErr who)) ∨
      ((¬ ∃ b ∈ σ.alarms, b.memberId = al.memberId ∧ b.kind = al.kind) ∧ σ' = σ ∧
          res = .ok (.alarm []) ∨
       (∃ b ∈ σ.alarms, b.memberId = al.memberId ∧ b.kind = al.kind) ∧
         σ' = { σ with alarms := σ.alarms.filter (fun b => ¬ (b.memberId = al.memberId ∧ b.kind = al.kind)) } ∧
         res = .ok (.alarm [al]))
  | _ => False

/-- **One request's linearized effect**: a refusal (any request, the state unchanged, an error of
`EtcdErr.refusal`), or the request's own step. `lo` (default `0`: any auth state the cluster has had)
is the index of the auth state when the call started: a linearizable read's permission is checked
at an auth state from `lo` on (`State.permittedSince`, `State.deniedSince`); the client's read specs
pass the `lo` the caller knows (`authLb`). The principal `who` is the one the server uses with auth
on (the token's user, else the client certificate's common name); with auth off no check depends
on it, so the certificate's name used then (`AuthInfoFromTLS`) is covered by every `who`. -/
def Step (who : Principal) (rq : Req) (σ σ' : State) (res : Resp) (lo : Nat := 0) : Prop :=
  (σ' = σ ∧ ∃ e, e.refusal = true ∧ res = .err e) ∨
  kvStep who rq σ σ' res lo ∨ leaseStep who rq σ σ' res ∨ authStep who rq σ σ' res lo ∨
  clusterStep who rq σ σ' res

/-- **The cluster's configuration, as far as the environment's steps depend on it**: whether the
members run an auto-compactor (`--auto-compaction-retention` not `0`), and whether leases may expire
during the run. Fixed when the cluster's
state is allocated (the cluster contract); every member is configured alike. -/
structure EnvCfg where
  autoCompact : Bool
  /-- whether a lease may expire during the run (`false`: a deployment premise, every lease granted
  outlives the run, as `examples/etcd/leasegrant` assumes) -/
  leaseExpiry : Bool
  /-- how far behind the current revision the auto-compactor compacts (a revision-mode compactor's
  retention; `0` for the periodic mode or none) -/
  compactLag : Nat

/-- Every environment step allowed (what `Reach` closes over). -/
def EnvCfg.all : EnvCfg := { autoCompact := true, leaseExpiry := true, compactLag := 0 }

/-- **The environment's steps** in a cluster configured as `cfg`: what no client call causes. A live
lease expires and the leader revokes it (its keys deleted at one revision); the server's
auto-compaction, if configured (at a revision it read: at most the current one); an alarm raised
(the quota exceeded, a corruption check); a member publishing its name and client URLs
(`publishV3`). -/
inductive EnvStep (cfg : EnvCfg) : State → State → Prop
  | leaseExpire (σ : State) (id : Int) (l : List KV) : cfg.leaseExpiry = true →
      σ.leases id ≠ none → σ.attachedKVs id l → EnvStep cfg σ (σ.revoke id l)
  | compact (σ : State) (r : Nat) : cfg.autoCompact = true →
      σ.kv.compacted < r → r + cfg.compactLag ≤ σ.kv.rev → EnvStep cfg σ (σ.withKV { σ.kv with compacted := r })
  | alarm (σ : State) (al : Alarm) : al.memberId < 2 ^ 64 →
      EnvStep cfg σ { σ with alarms := σ.alarms ++ [al] }
  | publish (σ : State) (id : Nat) (name : GoString) (urls : List GoString) :
      (∃ m ∈ σ.members, m.id = id) →
      EnvStep cfg σ { σ with members := σ.members.map (fun m => if m.id = id then { m with name := name, clientURLs := urls } else m) }

/-- **`σ'` is reachable from `σ`**: by any principal's steps and the environment's. -/
inductive Reach : State → State → Prop
  | refl (σ : State) : Reach σ σ
  | step (σ σ₁ σ' : State) (who : Principal) (rq : Req) (res : Resp) :
      Step who rq σ σ₁ res → Reach σ₁ σ' → Reach σ σ'
  | env (σ σ₁ σ' : State) : EnvStep EnvCfg.all σ σ₁ → Reach σ₁ σ' → Reach σ σ'

end EtcdModel
end EtcdGrove
end Perennial
