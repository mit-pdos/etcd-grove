/-
# `server/storage/schema`: etcd's buckets and their records (batch 4b): the vocabulary

The schema names etcd's backend buckets (`Key`, `Meta`, `Lease`, `Alarm`, `Cluster`, `Members`,
`MembersRemoved`, `Auth`, `AuthUsers`, `AuthRoles`) and reads and writes their records through a
backend transaction: the consistent index and term (`Meta`, big-endian `uint64`s), the lease records
(`Lease`, a `leasepb.Lease` under its id's bytes), the auth flags and records (`Auth`, `AuthUsers`,
`AuthRoles`), the members (`Members`, `MembersRemoved`: JSON), the alarms (`Alarm`).

## What the schema is stated over

The schema's functions take a transaction as an interface value (`backend.UnsafeReader`,
`UnsafeWriter`, `ReadTx`, `BatchTx`) and call its methods. **Their specs are stated over what they
need of such a transaction, not over etcd's backend** (PRINCIPLES, "An API is stated over the
abstractions it builds on"), as mvcc states its store over its storage contract:

* `txRd tx S R` (transparent, persistent): **reading through `tx`**, holding `R V` (the caller's
  view `V` of the buckets in its scope `S`): a single-key `UnsafeRange` (a `nil` end) returns the
  key's entry, `UnsafeForEach` calls its function on each entry once (in some order: a read
  transaction visits bolt's entries, then its buffer's). The bytes are bbolt's, **lent against
  `R V`** (`rangeK`, `lentIn`; the outer slices owned; the visitor's until `R V` is taken back,
  `lentKVs`), never readable after it (4c's `txBytes`).
* `txRange tx S R`: an interval `UnsafeRange` of a whole bucket, in key order (a batch transaction,
  or a read transaction of `key` only).
* `txWr tx S R` (transparent, persistent): **writing through `tx`**: `UnsafePut` (an entry bbolt
  accepts: `putFits`), `UnsafeDelete`, `UnsafeCreateBucket` (a bucket `S` may create:
  `S.canCreate`, separate from owning its keys) move `R V` to `R` of the changed view.
* `R : View → IProp` is the **caller's** family (its share of the backend: a lock-held batch view of
  its part, a read transaction's snapshot of it); `S : Scope` says which buckets and which keys of a
  shared bucket (`Meta`) are the caller's, so that a caller owning two keys of `Meta` (the consistent
  index) never claims the rest of it. The backend's laws producing these bundles for its
  transactions, at the families `Backend.btView` (the batch transaction, its lock held) and
  `Backend.rtView` (the shared read transaction, read-locked or under the batch lock), are in
  `backend/SchemaTx.lean` (imported by the server's proofs only, as mvcc's `MvccStorage.lean`).
* The struct methods that take a backend's locks themselves (`authBackend.GetUser`, `authBatchTx.Lock`,
  `ReadConsistentIndex`, ...) are stated with the triples of the backend calls they make as premises
  (`callOk`, `retOk`, `rdSect`): a wrapper's spec is its callee's, so the caller's own contract of
  the backend (with its lock invariant and post-lock hook) passes through unchanged.

So the schema's specs mention no predicate of the backend's: they hold of any transaction meeting the
bundles. What a caller reasons about is the view's **values**: the pure encodings below.

## Model (pure, transparent)

* `Bkt` (the buckets; `Bkt.name`, `Bkt.id`, `Bkt.safe`), the key names of `Meta`, `Auth`, `Cluster`.
* `BData` (a bucket's entries), `View` (each bucket's entries, or `none`: absent), `Scope`.
* `rangeOf m k e limit l` (`UnsafeRange`'s answer), `entsOf m l` (the entries in key order).
* `beU64 n` / `u64Of s`: `binary.BigEndian`'s eight bytes of a `uint64`, and its read of the first
  eight bytes (`Uint64` panics on fewer: `u64Ok`).
* The consistent index: `ciOf m` (the index and term `UnsafeReadConsistentIndex` reads, `0`: absent),
  `ciWf m` (their values have 8 bytes), `ciPut m i t` (`unsafeUpdateConsistentIndex`'s writes).
* Leases: `LeaseRec` (id, TTL, remaining TTL), `leaseModel` (a `leasepb.Lease` content's fields;
  opaque, with the message laws `leaseMsg_*`), `leaseEnc r v`, `leaseBktIs m L` (the bucket holds
  exactly the records of the table `L`, each under its id's bytes), `leaseAt p r` (a `*leasepb.Lease`
  holding `r`).
* Auth: `authEnabledOf m`, `authRevOf m` (the `Auth` bucket's flag and revision), `recsWf t m` (every
  value decodes as a `*t`: users, roles), `userName c`, `roleName c` (an `authpb.User`/`Role`
  content's name; opaque, provisional 3h's: 3h has no `authpb` vocabulary yet).
* Alarms and membership: `alarmEnts`, `alarmsAt`; `memberEnts`, `memberBktsAt` (the buckets' records,
  opaque encodings).
* `bucketAt b bv` (persistent): `bv` is the `backend.Bucket` value of `b` (a `schema.bucket` of its
  id, name and range flag): what the package's variables hold (`bucketVars_init.spec`); no address
  is a constant (the name slices are allocated at the package's initialization).

## Resources the schema owns (names-only parts: alarms, membership)

The alarm and membership backends are translated names only (assumed specs), each a struct over a
`backend.Backend` that takes the batch lock itself:
* `alarmBkt be al` (exclusive): **`be`'s `Alarm` bucket holds the alarms `al`** (as a set; `none`:
  no bucket yet), as the
  bucket's only writer sees it (2e's provisional `beAlarms`).
* `memberBkts be cb` (exclusive): **`be`'s `Members`, `MembersRemoved` and `Cluster` buckets hold
  `cb`** (`ClusterBkts`: 2e's view `ClusterSt`, the stored cluster version and downgrade info;
  `none`: not created yet; 2e's provisional `beMembers`).
Intended realization: 4a's ownership of those buckets, `be = Backend.beIface b` with `isBackend γ b
p Pk`: the part's batch image and visible image (`beCur`, `beVis` of the buckets, equal outside the
writer's sections, since their holder is their only writer), one reader slot (`beRdToks γ 1`: the
holder reads one at a time), an open share (`beOpen γ q`: `CreateAlarmBucket`,
`MustCreateBackendBuckets` lock outside apply), with the records' encodings (`alarmsAt`/`alarmEnts`:
an alarm the marshalled `AlarmMember` as the key, an empty value; `memberBktsAt`/`memberEnts`: a
member its id's string ↦ its JSON, a removed id ↦ `removed`, the cluster version its `String()`, the
downgrade info its JSON). Introduced from the opener's parts and given back for the backend's
close by `Backend.alarmBkt_intro`/`_elim`, `memberBkts_intro`/`_elim` (`backend/SchemaTx.lean`).
* The reads of these two (`GetAllAlarms`, `MustReadMembersFromBackend`) go through `be.ReadTx()`
  (the realization's slot; the specs still take and give back the caller's `threadTok`, which the
  bounds plan lends a reader slot for).
* `applyHook be Pre Q`: `be`'s batch transaction's `LockInsideApply` runs its post-lock hook from the
  caller's `Pre` to `Q`, and `Q` gives the lock's resource back for the wrapper's `Unlock`
  (realization: `isBackend`, an open share, a hook share, `Backend.hookRun γ q Pk f Pre Q'` and
  `Q' ={⊤}=∗ Pk ∗ Q`; introduced by `Backend.applyHook_intro`, which hands the two shares back
  inside `Q`).

## Users

The consistent index (2d's `cindex`: `ReadConsistentIndex`, `UnsafeUpdateConsistentIndex` in the
pre-commit hook), mvcc (3e: `UnsafeCreateMetaBucket`, the bucket values, the compaction key names),
the lessor (3c: `UnsafeCreateLeaseBucket`, `MustUnsafeGetAllLeases`, `MustUnsafePutLease`,
`UnsafeDeleteLease`), the auth store (3d: `NewAuthBackend` and every `AuthBackend`/`AuthBatchTx`/
`AuthReadTx` method), the alarm store (2e: `NewAlarmBackend`, `CreateAlarmBucket`, `MustPutAlarm`,
`MustDeleteAlarm`, `GetAllAlarms`), the membership (2e: `NewMembershipBackend`,
`MustSaveMemberToBackend`, `MustDeleteMemberFromBackend`, `MustReadMembersFromBackend`), the storage
hooks (2e: `MustUnsafeSaveConfStateToBackend`). Snippets: `examples/specreq/schema/`.

## Laws

`bucketAt_persistent`, `bucketVars_init`, `keyNames_init`, `leaseMsg_of_struct`,
`leaseMsg_to_struct`, `alarmBkt_timeless`, `memberBkts_timeless`, `alarmBkt_excl`,
`memberBkts_excl`, `alarmEnts_empty`, `memberEnts_empty`. The laws relating the schema to the
backend (`bucketAt` gives `Backend.bucketOk`, the safe-range registry, the bundles, `applyHook`,
`alarmBkt`, `memberBkts`) are in `backend/SchemaTx.lean`: the schema does not import the backend.
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.schema
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasepb
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.storage.schema
public import Spec.google_golang_org.protobuf.proto.Api
public import Spec.go_etcd_io.etcd.api.v3.Model
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.bbolt.Model
public import Spec.github_com.Masterminds.semver.v3.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.version

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

/-! ## Model -/

section model
variable [GooseExts] [GoGlobalContext]

/-- **etcd's buckets** (`schema/bucket.go`). -/
inductive Bkt where
  | key | metaB | lease | alarm | cluster | members | membersRemoved | auth | authUsers | authRoles
  deriving DecidableEq

/-- A bucket's name. -/
def Bkt.name : Bkt → GoString
  | .key => go!"key" | .metaB => go!"meta" | .lease => go!"lease" | .alarm => go!"alarm"
  | .cluster => go!"cluster" | .members => go!"members" | .membersRemoved => go!"members_removed"
  | .auth => go!"auth" | .authUsers => go!"authUsers" | .authRoles => go!"authRoles"

/-- A bucket's id (`backend.BucketID`). -/
def Bkt.id : Bkt → w64
  | .key => W64 1 | .metaB => W64 2 | .lease => W64 3 | .alarm => W64 4 | .cluster => W64 5
  | .members => W64 10 | .membersRemoved => W64 11 | .auth => W64 20 | .authUsers => W64 21
  | .authRoles => W64 22

/-- Whether a bucket is a safe-range bucket (`Key` only). -/
def Bkt.safe : Bkt → Bool
  | .key => true | _ => false

/-- The key names (`bucket.go:72-86`). -/
def ciKey : GoString := go!"consistent_index"
def termKey : GoString := go!"term"
def confStateKey : GoString := go!"confState"
def storageVersionKey : GoString := go!"storageVersion"
def schedKey : GoString := go!"scheduledCompactRev"
def finKey : GoString := go!"finishedCompactRev"
def authEnabledKey : GoString := go!"authEnabled"
def authRevKey : GoString := go!"authRevision"
def clusterVersionKey : GoString := go!"clusterVersion"
def downgradeKey : GoString := go!"downgrade"

/-- **A bucket's entries.** -/
abbrev BData := GoString → Option GoString

/-- **A view of the buckets**: each one's entries, or `none` (absent). -/
abbrev View := Bkt → Option BData

def BData.empty : BData := fun _ => none

def BData.put (m : BData) (k v : GoString) : BData := fun k' => if k' = k then some v else m k'

def BData.del (m : BData) (k : GoString) : BData := fun k' => if k' = k then none else m k'

def View.put (V : View) (b : Bkt) (k v : GoString) : View :=
  fun b' => if b' = b then (V b).map (·.put k v) else V b'

def View.del (V : View) (b : Bkt) (k : GoString) : View :=
  fun b' => if b' = b then (V b).map (·.del k) else V b'

/-- `b`'s entries replaced by `m`. -/
def View.set (V : View) (b : Bkt) (m : BData) : View :=
  fun b' => if b' = b then some m else V b'

/-- `UnsafeCreateBucket(b)`: `b` exists (unchanged if it did). -/
def View.create (V : View) (b : Bkt) : View :=
  fun b' => if b' = b then some ((V b).getD BData.empty) else V b'

/-- **A caller's scope**: for each bucket, the keys of it that are the caller's (`none`: all of
them; `some ks`: those of a shared bucket, `Meta`), and whether the caller may create it. Creating a
bucket changes no key, and etcd never deletes these buckets, so the right to create is separate
from the keys (mvcc creates `Meta` and owns two of its keys; the consistent index owns two others). -/
structure Scope where
  keys : Bkt → Option (List GoString)
  create : Bkt → Bool

def Scope.whole (S : Scope) (b : Bkt) : Prop := S.keys b = none

def Scope.has (S : Scope) (b : Bkt) (k : GoString) : Prop :=
  match S.keys b with
  | none => True
  | some ks => k ∈ ks

/-- `S` may create `b`. -/
def Scope.canCreate (S : Scope) (b : Bkt) : Prop := S.create b = true

/-- The scope of exactly these buckets, whole, with the right to create them. -/
def Scope.ofBkts (bs : List Bkt) : Scope :=
  ⟨fun b => if b ∈ bs then none else some [], fun b => decide (b ∈ bs)⟩

/-- The consistent index's scope: two keys of `Meta`, no bucket to create. -/
def ciScope : Scope :=
  ⟨fun b => if b = .metaB then some [ciKey, termKey] else some [], fun _ => false⟩

/-- **The entries of `m` in some order, each once** (`UnsafeForEach` of a read transaction visits
bolt's entries, then the buffer's: not sorted as a whole). -/
def entsAny (m : BData) (l : List (GoString × GoString)) : Prop :=
  ∃ le, (∀ x, x ∈ le ↔ m x.1 = some x.2) ∧ le.Pairwise (fun a b => a.1 ≠ b.1) ∧ l.Perm le

open Classical in
/-- **`UnsafeRange(b, k, e, limit)`'s answer from the entries `m`**: an empty `e` the key `k` alone;
else the entries of `[k, e)` in key order, cut at a positive `limit`. -/
def rangeOf (m : BData) (k e : GoString) (limit : Int) (l : List (GoString × GoString)) : Prop :=
  if e = [] then l = (match m k with | some v => [(k, v)] | none => [])
  else ∃ all : List (GoString × GoString),
    all.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧
    (∀ x, x ∈ all ↔ (go.GoStringLe k x.1 ∧ go.GoStringLt x.1 e ∧ m x.1 = some x.2)) ∧
    l = (if 0 < limit ∧ limit < all.length then all.take limit.toNat else all)

/-- **The entries of `m` in key order.** -/
def entsOf (m : BData) (l : List (GoString × GoString)) : Prop :=
  l.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧ ∀ x, x ∈ l ↔ m x.1 = some x.2

/-- **`binary.BigEndian.PutUint64`'s eight bytes.** -/
def beU64 (n : w64) : GoString :=
  (List.range 8).map (fun i => W8 ((uint.Z n / 2 ^ (8 * (7 - i))) % 256))

/-- **`binary.BigEndian.Uint64(s)`** (of its first eight bytes). -/
def u64Of (s : GoString) : w64 :=
  W64 ((s.take 8).foldl (fun acc b => acc * 256 + uint.Z b) 0)

/-- `Uint64(s)` does not panic: eight bytes at least. -/
def u64Ok (s : GoString) : Prop := 8 ≤ s.length

/-- **The consistent index and term `Meta` holds** (`UnsafeReadConsistentIndex`: `(0, 0)` without an
index; the term `0` without a term). -/
def ciOf (m : BData) : w64 × w64 :=
  match m ciKey with
  | none => (W64 0, W64 0)
  | some v => (u64Of v, match m termKey with | none => W64 0 | some t => u64Of t)

/-- The stored index and term have eight bytes (what `unsafeUpdateConsistentIndex` writes). -/
def ciWf (m : BData) : Prop :=
  (∀ v, m ciKey = some v → u64Ok v) ∧ (∀ v, m termKey = some v → u64Ok v)

/-- **`unsafeUpdateConsistentIndex`'s writes**: nothing at index `0`; else the index, and the term
unless `0`. -/
def ciPut (m : BData) (i t : w64) : BData :=
  if i = W64 0 then m
  else if t = W64 0 then m.put ciKey (beU64 i)
  else (m.put ciKey (beU64 i)).put termKey (beU64 t)

/-- **A lease record**: id, TTL, remaining TTL (`leasepb.Lease`'s fields). -/
abbrev LeaseRec := w64 × w64 × w64

/-- **The fields of a `leasepb.Lease` content** (opaque: what `proto.Unmarshal` puts in them). -/
opaque leaseModel : Proto.Content → LeaseRec

/-- **`v` is a lease record's encoding**: `proto.Marshal` of a `leasepb.Lease` with its fields. -/
def leaseEnc (r : LeaseRec) (v : GoString) : Prop :=
  ∃ c, leaseModel c = r ∧ Proto.encodes go_etcd_io.etcd.server.v3.lease.leasepb.Lease.ty c v ∧
    Proto.depth c < Proto.depthMax

/-- **The `Lease` bucket holds exactly the records of `L`** (each under its id's eight bytes). -/
def leaseBktIs (m : BData) (L : w64 → Option LeaseRec) : Prop :=
  ∀ k v, m k = some v ↔ ∃ id r, k = beU64 id ∧ L id = some r ∧ r.1 = id ∧ leaseEnc r v

/-- **The `Auth` bucket's enabled flag** (`authEnabled` holding `[1]`). -/
def authEnabledOf (m : BData) : Bool := decide (m authEnabledKey = some [W8 1])

/-- **The `Auth` bucket's revision** (`0`: absent). -/
def authRevOf (m : BData) : w64 :=
  match m authRevKey with | none => W64 0 | some v => u64Of v

/-- The stored revision has eight bytes. -/
def authRevWf (m : BData) : Prop := ∀ v, m authRevKey = some v → u64Ok v

/-- **Every value of `m` decodes as a `*t`** (users, roles: `proto.Unmarshal` succeeds; Go panics
otherwise). -/
def recsWf (t : go.GoType) (m : BData) : Prop :=
  ∀ k v, m k = some v → ∃ c, Proto.encodes t c v ∧ Proto.depth c < Proto.depthMax

/-- (provisional, 3h's `authpb`) **An `authpb.User` content's name.** -/
opaque userName : Proto.Content → GoString
/-- (provisional, 3h's `authpb`) **An `authpb.Role` content's name.** -/
opaque roleName : Proto.Content → GoString

/-- (provisional, 3h's `etcdserverpb`) **An `AlarmMember` content holds the alarm `a`** (its
member id and type). -/
opaque alarmMemberIs : Proto.Content → EtcdModel.Alarm → Prop

open Classical in
/-- An alarm set with `a` (no duplicates). -/
def alarmsIns (al : List EtcdModel.Alarm) (a : EtcdModel.Alarm) : List EtcdModel.Alarm :=
  if a ∈ al then al else al ++ [a]

open Classical in
/-- An alarm set without `a`. -/
def alarmsDel (al : List EtcdModel.Alarm) (a : EtcdModel.Alarm) : List EtcdModel.Alarm :=
  al.filter (fun x => decide (x ≠ a))

/-- **The membership buckets' contents** (`Members`, `MembersRemoved`, `Cluster`): the members and
removed ids (2e's view), the stored cluster version (`String()` of a version), the stored downgrade
info (`Enabled`, `TargetVersion`). -/
structure ClusterBkts where
  st : Membership.ClusterSt
  ver : Option Semver.SemVer
  dg : Option (Bool × GoString)

/-- **A member's JSON fits a bbolt entry** (`json.Marshal` escapes a byte to at most six; the ids,
flags and punctuation within 1024 bytes): a bound on the member's strings. -/
def memberFits (mm : EtcdModel.Member) : Prop :=
  6 * (mm.name.length + ((mm.peerURLs ++ mm.clientURLs).map List.length).sum +
    4 * (mm.peerURLs ++ mm.clientURLs).length) + 1024 ≤ Bbolt.bboltEntryMax

/-- Fresh buckets: nothing stored. -/
def ClusterBkts.empty : ClusterBkts := ⟨⟨[], []⟩, none, none⟩

/-- **The `Alarm` bucket's entries are the alarms `al`'s records** (opaque: the protobuf encoding):
each key a marshalled `AlarmMember` (`alarmMemberIs`) of an alarm of `al`, its value empty, each
alarm of `al` (no duplicates) under exactly one key. -/
opaque alarmEnts (m : BData) (al : List EtcdModel.Alarm) : Prop

/-- **The bucket `o` (`none`: absent) holds the alarms `al`** (`none`: absent). -/
def alarmsAt (o : Option BData) (al : Option (List EtcdModel.Alarm)) : Prop :=
  match o, al with
  | none, none => True
  | some m, some al => alarmEnts m al
  | _, _ => False

/-- **The membership buckets' entries are `cb`'s records** (opaque: the JSON encodings; see the
header): `Members` a member's id string ↦ its JSON, `MembersRemoved` a removed id ↦ `removed`,
`Cluster` the cluster version's `String()` and the downgrade info's JSON. -/
opaque memberEnts (mem rem cl : BData) (cb : ClusterBkts) : Prop

/-- **The view's membership buckets hold `cb`** (`none`: each of the three absent or empty). -/
def memberBktsAt (V : View) (cb : Option ClusterBkts) : Prop :=
  match cb with
  | none => ∀ b ∈ [Bkt.members, .membersRemoved, .cluster], V b = none ∨ V b = some BData.empty
  | some cb => ∃ mem rem cl, V .members = some mem ∧ V .membersRemoved = some rem ∧
      V .cluster = some cl ∧ memberEnts mem rem cl cb

/-- **An entry lent to an `UnsafeForEach` visitor**: its key and value, the slices holding them
and the fraction (bbolt's memory, or the read buffer's). -/
structure LentKV where
  k : GoString
  v : GoString
  ks : GoSlice
  vs : GoSlice
  dq : DFrac

def LentKV.ent (x : LentKV) : GoString × GoString := (x.k, x.v)

end model

/-! ## Values and resources -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`v` is a `schema.bucket` of `b`**: its id, its name (read-only for good), its range flag. -/
def bucketIs (b : Bkt) (v : go_etcd_io.etcd.server.v3.storage.schema.bucket) : IProp GF :=
  iprop(⌜v.id' = b.id ∧ v.safeRangeBucket' = b.safe⌝ ∗ v.name' ↦*□ b.name)

/-- **`bv` is the `backend.Bucket` value of `b`** (persistent). -/
def bucketAt (b : Bkt) (bv : GoInterface) : IProp GF :=
  iprop(∃ v, ⌜bv = interface.mkOk go_etcd_io.etcd.server.v3.storage.schema.bucket.ty #v⌝ ∗
    bucketIs b v)

/-- The package variable of each bucket. -/
def Bkt.var : Bkt → GoString
  | .key => go_etcd_io.etcd.server.v3.storage.schema.Key
  | .metaB => go_etcd_io.etcd.server.v3.storage.schema.Meta
  | .lease => go_etcd_io.etcd.server.v3.storage.schema.Lease
  | .alarm => go_etcd_io.etcd.server.v3.storage.schema.Alarm
  | .cluster => go_etcd_io.etcd.server.v3.storage.schema.Cluster
  | .members => go_etcd_io.etcd.server.v3.storage.schema.Members
  | .membersRemoved => go_etcd_io.etcd.server.v3.storage.schema.MembersRemoved
  | .auth => go_etcd_io.etcd.server.v3.storage.schema.Auth
  | .authUsers => go_etcd_io.etcd.server.v3.storage.schema.AuthUsers
  | .authRoles => go_etcd_io.etcd.server.v3.storage.schema.AuthRoles

/-- **Byte slices lent by a transaction**: the slice `sl` (owned: the backend's fresh `append`s)
of slices holding `l`, each at the fraction `dq` (bbolt's memory, valid while the transaction is:
4c's `txBytes`). -/
def lentBytes (sl : GoSlice) (dq : DFrac) (l : List GoString) (ps : List GoSlice) : IProp GF :=
  iprop(sl ↦* ps ∗ [∗list] p; b ∈ ps; l, p ↦*{dq} b)

/-- The lent slices' contents alone (what is given back for the view). -/
def lentIn (dq : DFrac) (l : List GoString) (ps : List GoSlice) : IProp GF :=
  iprop([∗list] p; b ∈ ps; l, p ↦*{dq} b)

/-- **`UnsafeRange`'s continuation**: the answer `l` (`rangeOf`), its keys and values lent against
the view `R V` (given back with them; the outer slices owned, as the backend's `rangeRes`). -/
def rangeK (R : View → IProp GF) (V : View) (m : BData) (k e : GoString) (limit : w64)
    (Ψ : val → IProp GF) : IProp GF :=
  iprop(∀ (kl vl : GoSlice) (l : List (GoString × GoString)) (dq : DFrac) (ps qs : List GoSlice),
    ⌜rangeOf m k e (sint.Z limit) l⌝ -∗ kl ↦* ps -∗ vl ↦* qs -∗
    lentIn dq (l.map Prod.fst) ps -∗ lentIn dq (l.map Prod.snd) qs -∗
    (lentIn dq (l.map Prod.fst) ps -∗ lentIn dq (l.map Prod.snd) qs -∗ R V) -∗
    Ψ (PairV #kl #vl))

/-- **The bytes lent to the visitor so far**, given back for the view. -/
def lentKVs (l : List LentKV) : IProp GF :=
  iprop([∗list] x ∈ l, x.ks ↦*{x.dq} x.k ∗ x.vs ↦*{x.dq} x.v)

/-- **Reading through `tx`** with the caller's view `R V` of its scope `S` (see the header):
`UnsafeRange(b, k, nil, 0)` of a key of the caller's, of an existing bucket (a `nil` end: a
non-`nil` empty end makes etcd's read transaction range the bucket, which panics outside `key`), and
`UnsafeForEach` of a whole bucket of `S`, calling `f(k, v)` on each entry once (a read
transaction: bolt's entries, then its buffer's; not sorted as a whole), until `f` returns an error,
which it returns; the bytes are lent to the visitor, which may keep them (`unsafeGetAllUsers`
appends the value slices and unmarshals them after the loop) until it gives them back for `R V`
(`lentKVs`; also after an error, `J` over the entries visited before it: a failing call gives its
own entry's bytes back, integration Y). The bytes are bbolt's: lent against `R V`, never readable
after it (4c's `txBytes`, read against a share of the transaction's liveness `Bbolt.txLive`). -/
def txRd (tx : GoInterface) (S : Scope) (R : View → IProp GF) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tx = GoInterface.ok i⌝ ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (ks : GoSlice) (k : GoString)
        (dk : DFrac) (limit : w64) (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.has b k⌝ -∗ ks ↦*{dk} k -∗
      ▷ (ks ↦*{dk} k -∗ rangeK R V m k [] limit Φ) -∗
      WP (App (App (App (App (Val #(methods i.ty go!"UnsafeRange" i.v)) (Val #bv)) (Val #ks))
        (Val #slice.nil)) (Val #limit)) {{ Φ }}) ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (f : GoFunc)
        (I : List LentKV → IProp GF) (J : List LentKV → GoInterface → IProp GF)
        (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.whole b⌝ -∗ I [] -∗
      (□ ∀ (pre : List LentKV) (k v : GoString) (ks vs : GoSlice) (dq : DFrac),
        I pre -∗ ks ↦*{dq} k -∗ vs ↦*{dq} v -∗
        WP (App (App (Val #f) (Val #ks)) (Val #vs)) {{ r, ∃ err : GoInterface, ⌜r = #err⌝ ∗
          ((⌜err = GoInterface.nil⌝ ∗ I (pre ++ [⟨k, v, ks, vs, dq⟩])) ∨
           (⌜err ≠ GoInterface.nil⌝ ∗ ks ↦*{dq} k ∗ vs ↦*{dq} v ∗ J pre err)) }}) -∗
      ▷ (∀ err : GoInterface,
          ((⌜err = GoInterface.nil⌝ ∗ ∃ l, ⌜entsAny m (l.map LentKV.ent)⌝ ∗ I l ∗
              (lentKVs l -∗ R V)) ∨
           (⌜err ≠ GoInterface.nil⌝ ∗ ∃ l, J l err ∗ (lentKVs l -∗ R V))) -∗ Φ #err) -∗
      WP (App (App (Val #(methods i.ty go!"UnsafeForEach" i.v)) (Val #bv)) (Val #f)) {{ Φ }}))

/-- **Ranges through `tx`** of a whole bucket of the caller's, in key order (`UnsafeRange` with an
end: a batch transaction's, or a read transaction's of a safe-range bucket only: etcd's read
transactions panic on an interval range of another bucket,
`nonissues/etcd-auth-readtx-getallroles-panics.md`); an empty end only as `nil`. Bytes lent, as
`txRd`. -/
def txRange (tx : GoInterface) (S : Scope) (R : View → IProp GF) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tx = GoInterface.ok i⌝ ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (ks es : GoSlice) (k e : GoString)
        (dk de : DFrac) (limit : w64) (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.whole b ∧ (e = [] → es = slice.nil)⌝ -∗
      ks ↦*{dk} k -∗ es ↦*{de} e -∗
      ▷ (ks ↦*{dk} k -∗ es ↦*{de} e -∗ rangeK R V m k e limit Φ) -∗
      WP (App (App (App (App (Val #(methods i.ty go!"UnsafeRange" i.v)) (Val #bv)) (Val #ks))
        (Val #es)) (Val #limit)) {{ Φ }}))

/-- **An entry bbolt accepts**: a non-empty key within `maxKeySize`, key and value within
`bboltEntryMax` (else `batchTx.unsafePut` is `Fatal`). -/
def putFits (k v : GoString) : Prop :=
  k ≠ [] ∧ k.length ≤ Bbolt.maxKeySize ∧ k.length + v.length ≤ Bbolt.bboltEntryMax

/-- **Writing through `tx`** (the batch transaction, its lock held, the caller's view `R V` of its
scope `S`; see the header): `UnsafePut` (a key of the caller's, of an existing bucket, an entry
bbolt accepts: `putFits`; the bytes read-only for good, the backend's buffer keeps them),
`UnsafeDelete`, `UnsafeCreateBucket` (a bucket the caller may create). -/
def txWr (tx : GoInterface) (S : Scope) (R : View → IProp GF) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tx = GoInterface.ok i⌝ ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (ks vs : GoSlice) (k v : GoString)
        (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.has b k ∧ putFits k v⌝ -∗ ks ↦*□ k -∗ vs ↦*□ v -∗
      ▷ (R (V.put b k v) -∗ Φ #()) -∗
      WP (App (App (App (Val #(methods i.ty go!"UnsafePut" i.v)) (Val #bv)) (Val #ks)) (Val #vs))
        {{ Φ }}) ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (ks : GoSlice) (k : GoString)
        (dk : DFrac) (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.has b k⌝ -∗ ks ↦*{dk} k -∗
      ▷ (R (V.del b k) -∗ ks ↦*{dk} k -∗ Φ #()) -∗
      WP (App (App (Val #(methods i.ty go!"UnsafeDelete" i.v)) (Val #bv)) (Val #ks)) {{ Φ }}) ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜S.canCreate b⌝ -∗ ▷ (R (V.create b) -∗ Φ #()) -∗
      WP (App (Val #(methods i.ty go!"UnsafeCreateBucket" i.v)) (Val #bv)) {{ Φ }}))

/-- **`recv.m()` from `P` returns, giving `Q`** (one use: a backend call a wrapper makes). -/
def callOk (recv : GoInterface) (m : GoString) (P Q : IProp GF) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜recv = GoInterface.ok i⌝ ∗
    (P -∗ WP (App (Val #(methods i.ty m i.v)) (Val #())) {{ v, ⌜v = #()⌝ ∗ Q }}))

/-- **`recv.m()` returns `r`, at any time** (persistent: `Backend.BatchTx()`, `ReadTx()`). -/
def retOk (recv : GoInterface) (m : GoString) (r : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜recv = GoInterface.ok i⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #r -∗ WP (App (Val #(methods i.ty m i.v)) (Val #())) {{ Φ }})

/-- **A read section on `tx`**: `RLock()` from `P` gives the caller's view `R V` with `ok V`;
`RUnlock()` from `R V` gives `Q V` (one use each). -/
def rdSect (tx : GoInterface) (P : IProp GF) (R : View → IProp GF) (ok : View → Prop)
    (Q : View → IProp GF) : IProp GF :=
  iprop(callOk tx go!"RLock" P iprop(∃ V, R V ∗ ⌜ok V⌝) ∗
    ∃ i : GoInterfaceOk, ⌜tx = GoInterface.ok i⌝ ∗
      ∀ V, R V -∗ WP (App (Val #(methods i.ty go!"RUnlock" i.v)) (Val #())) {{ v, ⌜v = #()⌝ ∗ Q V }})

/-- **A write section on the batch transaction `tx`**: `lock()` (`LockInsideApply`,
`LockOutsideApply`) from `P` gives the caller's view `R V` with `ok V`; `Unlock()` from `R V` gives
`Q V` (one use each). -/
def wrSect (tx : GoInterface) (lock : GoString) (P : IProp GF) (R : View → IProp GF)
    (ok : View → Prop) (Q : View → IProp GF) : IProp GF :=
  iprop(callOk tx lock P iprop(∃ V, R V ∗ ⌜ok V⌝) ∗
    ∃ i : GoInterfaceOk, ⌜tx = GoInterface.ok i⌝ ∗
      ∀ V, R V -∗ WP (App (Val #(methods i.ty go!"Unlock" i.v)) (Val #())) {{ v, ⌜v = #()⌝ ∗ Q V }})

/-- **A `*leasepb.Lease` holding `r`** (owned). -/
def leaseAt (p : Loc) (r : LeaseRec) : IProp GF :=
  iprop(∃ v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease, p ↦ v ∗
    ⌜v.ID' = r.1 ∧ v.TTL' = r.2.1 ∧ v.RemainingTTL' = r.2.2⌝)

/-- **What `UnsafeGetUser`/`UnsafeGetRole` returns for the value `o`**: `nil` without one, else a
fresh `*t` holding a content the value encodes. -/
def recRes (t : go.GoType) (o : Option GoString) (p : Loc) : IProp GF :=
  match o with
  | none => iprop(⌜p = null⌝)
  | some v => iprop(∃ c, Proto.msgAt t p (DFrac.own 1) c ∗ ⌜Proto.encodes t c v⌝)

/-- **A slice of fresh `*t` decoding the values `l`** (`nil` if `l` is empty). -/
def recsRes (t : go.GoType) (sl : GoSlice) (l : List GoString) : IProp GF :=
  iprop(⌜l = [] → sl = slice.nil⌝ ∗ ∃ ps : List Loc, sl ↦* ps ∗
    [∗list] p; v ∈ ps; l, ∃ c, Proto.msgAt t p (DFrac.own 1) c ∗ ⌜Proto.encodes t c v⌝)

/-- **`be`'s `Alarm` bucket holds `al`** (`none`: absent; exclusive; see the header). The heap
binder is in the signature (an opaque body drops unused section variables). -/
opaque alarmBkt [GooseSemantics] [GooseInterp] [HeapGS HasLC.hasLC GF] (be : GoInterface)
    (al : Option (List EtcdModel.Alarm)) : IProp GF := iprop(True)

/-- **`be`'s membership buckets hold `cb`** (`none`: not created yet; exclusive; see the header). -/
opaque memberBkts [GooseSemantics] [GooseInterp] [HeapGS HasLC.hasLC GF] (be : GoInterface)
    (cb : Option ClusterBkts) : IProp GF := iprop(True)

/-- **`be`'s `LockInsideApply` runs its post-lock hook from `Pre` to `Q`, and the wrapper's
`Unlock` gets the lock's resource back** (one use; see the header). Introduced from the backend's
`hookRun` by `Backend.applyHook_intro` (`backend/SchemaTx.lean`). -/
opaque applyHook [GooseSemantics] [GooseInterp] [HeapGS HasLC.hasLC GF] (be : GoInterface)
    (Pre Q : IProp GF) : IProp GF := iprop(True)

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def bucketAt_persistent.spec : Prop := ∀ b bv, Persistent (bucketAt (GF := GF) b bv)

/-- **The package's bucket variables** (the package's initialization). Of the buckets only `Key`,
`Meta`, `Lease` and the auth buckets have translated initializers; `Alarm`, `Cluster`, `Members`,
`MembersRemoved` are names only, so their rows rest on `etc/gen-init.py`'s trust-boundary axioms for
untranslated initializers (a struct literal of a translated type and a `[]byte` literal). -/
def bucketVars_init.spec : Prop := ∀ b : Bkt,
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢
    ∃ bv, globalAddr b.var ↦□ bv ∗ bucketAt b bv

/-- **The package's key-name variables** hold their names, read-only for good (mvcc's compaction
keys among them, 3e). `ScheduledCompactKeyName`, `FinishedCompactKeyName`, `MetaConfStateName` are
names only: their rows rest on `etc/gen-init.py`'s trust axioms for untranslated initializers (each a
`[]byte` literal). -/
def keyNames_init.spec : Prop := ∀ (var name : GoString),
  (var, name) ∈ [(go_etcd_io.etcd.server.v3.storage.schema.MetaConsistentIndexKeyName, ciKey),
    (go_etcd_io.etcd.server.v3.storage.schema.MetaTermKeyName, termKey),
    (go_etcd_io.etcd.server.v3.storage.schema.ScheduledCompactKeyName, schedKey),
    (go_etcd_io.etcd.server.v3.storage.schema.FinishedCompactKeyName, finKey),
    (go_etcd_io.etcd.server.v3.storage.schema.MetaConfStateName, confStateKey),
    (go_etcd_io.etcd.server.v3.storage.schema.AuthEnabledKeyName, authEnabledKey),
    (go_etcd_io.etcd.server.v3.storage.schema.AuthRevisionKeyName, authRevKey),
    (go_etcd_io.etcd.server.v3.storage.schema.authEnabled, [W8 1]),
    (go_etcd_io.etcd.server.v3.storage.schema.authDisabled, [W8 0])] →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢
    ∃ sl : GoSlice, globalAddr var ↦□ sl ∗ sl ↦*□ name

/-- **An owned `leasepb.Lease` struct is a message holding its fields** (one way: `Marshal`
writes the message's `sizeCache`; `leaseMsg_to_struct` gives the struct back). -/
def leaseMsg_of_struct.spec : Prop := ∀ (p : Loc)
    (v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease),
  (p ↦ v : IProp GF) ⊢ ∃ c, Proto.msgAt go_etcd_io.etcd.server.v3.lease.leasepb.Lease.ty p (DFrac.own 1) c ∗
    ⌜leaseModel c = (v.ID', v.TTL', v.RemainingTTL') ∧ c.fits ∧ Proto.marshalOk c⌝

/-- **An owned `leasepb.Lease` message is a struct holding its fields.** -/
def leaseMsg_to_struct.spec : Prop := ∀ (p : Loc) (c : Proto.Content),
  Proto.msgAt (GF := GF) go_etcd_io.etcd.server.v3.lease.leasepb.Lease.ty p (DFrac.own 1) c ⊢
    leaseAt p (leaseModel c)

def alarmBkt_timeless.spec : Prop := ∀ be al, Timeless (alarmBkt (GF := GF) be al)
def alarmBkt_excl.spec : Prop := ∀ be al al',
  alarmBkt (GF := GF) be al ∗ alarmBkt be al' ⊢ iprop(False)
def memberBkts_timeless.spec : Prop := ∀ be st, Timeless (memberBkts (GF := GF) be st)
def memberBkts_excl.spec : Prop := ∀ be st st',
  memberBkts (GF := GF) be st ∗ memberBkts be st' ⊢ iprop(False)

/-- An empty `Alarm` bucket holds no alarm (`CreateAlarmBucket` on a fresh member). -/
def alarmEnts_empty.spec : Prop := alarmEnts BData.empty []

/-- Empty membership buckets hold nothing (`MustCreateBackendBuckets` on a fresh member). -/
def memberEnts_empty.spec : Prop :=
  memberEnts BData.empty BData.empty BData.empty ClusterBkts.empty

end laws

end Schema
end EtcdGrove
end Perennial
