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
  view `V` of the buckets in its scope `S`, kept): `UnsafeRange` of a bucket returns the range of
  `V`'s entries, `UnsafeForEach` calls its function on them in key order.
* `txWr tx S R` (transparent, persistent): **writing through `tx`**: `UnsafePut`, `UnsafeDelete`,
  `UnsafeCreateBucket` move `R V` to `R` of the changed view.
* `R : View → IProp` is the **caller's** family (its share of the backend: a lock-held batch view of
  its part, a read transaction's snapshot of it); `S : Scope` says which buckets and which keys of a
  shared bucket (`Meta`) are the caller's, so that a caller owning two keys of `Meta` (the consistent
  index) never claims the rest of it. The backend (4a) proves these bundles of its transactions for
  the parts it hands out (`req/go_etcd_io_etcd_server_v3_storage_backend.md`, "from 4b").
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
  content's name; opaque, provisional 3h's).
* `bucketAt b bv` (persistent): `bv` is the `backend.Bucket` value of `b` (a `schema.bucket` of its
  id, name and range flag): what the package's variables hold (`bucketVars_init.spec`); no address
  is a constant (the name slices are allocated at the package's initialization).

## Resources the schema owns (names-only parts: alarms, membership)

The alarm and membership backends are translated names only (assumed specs), each a struct over a
`backend.Backend` that takes the batch lock itself:
* `alarmBkt be al` (exclusive): **`be`'s `Alarm` bucket holds the alarms `al`** (as a set; `none`:
  no bucket yet), as the
  bucket's only writer sees it (2e's provisional `beAlarms`).
* `memberBkts be st` (exclusive): **`be`'s `Members` and `MembersRemoved` buckets hold the view
  `st`** (2e's `ClusterSt`; 2e's provisional `beMembers`).
Intended realization: 4a's ownership of those buckets (the batch view, equal to the published one
outside the writer's sections, since their holder is their only writer) with the records' encodings
(an alarm: the marshalled `AlarmMember` as the key, an empty value; a member: its id's string ↦ its
JSON; a removed id ↦ `removed`). Introduced by the backend's opener (2e's `OpenBackend` over 4a).
* The reads of these two (`GetAllAlarms`, `MustReadMembersFromBackend`) go through `be.ReadTx()`:
  each takes the caller's `threadTok` for its reader slot (the bounds plan) and gives it back.
* `applyHook be Pre Q` (provisional, 4a's): `be`'s batch transaction's `LockInsideApply` runs its
  post-lock hook from the caller's `Pre` to `Q` (3c's `beHook` with `Mvcc.hookRun`).

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

`bucketAt_persistent`, `bucketAt_agree`, `bucketVars_init`, `keyNames_init`, `leaseMsg_of_struct`,
`leaseMsg_to_struct`, `alarmBkt_timeless`, `memberBkts_timeless`, `alarmBkt_excl`,
`memberBkts_excl`.
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.schema
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasepb
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.storage.schema
public import Spec.google_golang_org.protobuf.proto.Api
public import Spec.go_etcd_io.etcd.api.v3.Model
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_uber_org.zap.Api

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

/-- **A caller's scope**: for each bucket, `none` (the whole bucket, its existence included) or the
keys of it that are the caller's (a shared bucket: `Meta`). -/
abbrev Scope := Bkt → Option (List GoString)

def Scope.whole (S : Scope) (b : Bkt) : Prop := S b = none

def Scope.has (S : Scope) (b : Bkt) (k : GoString) : Prop :=
  match S b with
  | none => True
  | some ks => k ∈ ks

/-- A range `S` allows: any range of a whole bucket, a single key (empty end) of the caller's. -/
def Scope.reads (S : Scope) (b : Bkt) (k e : GoString) : Prop :=
  S.whole b ∨ (e = [] ∧ S.has b k)

/-- The scope of exactly these buckets, whole. -/
def Scope.ofBkts (bs : List Bkt) : Scope := fun b => if b ∈ bs then none else some []

/-- The consistent index's scope: two keys of `Meta`. -/
def ciScope : Scope := fun b => if b = .metaB then some [ciKey, termKey] else some []

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

/-- A slice of byte slices, read-only, holding `l`. -/
def bytesListAt (sl : GoSlice) (l : List GoString) : IProp GF :=
  iprop(∃ ps : List GoSlice, sl ↦*□ ps ∗ [∗list] p; b ∈ ps; l, p ↦*□ b)

/-- **Reading through `tx`** with the caller's view `R V` of its scope `S` (kept; see the header):
`UnsafeRange` of a single key of the caller's (an empty end), of an existing bucket, and
`UnsafeForEach` (of a whole bucket of
`S`, calling `f(k, v)` on its entries in key order, the bytes read-only, until `f` returns an error,
which it returns). -/
def txRd (tx : GoInterface) (S : Scope) (R : View → IProp GF) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tx = GoInterface.ok i⌝ ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (ks es : GoSlice) (k e : GoString)
        (dk de : DFrac) (limit : w64) (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ e = [] ∧ S.has b k⌝ -∗ ks ↦*{dk} k -∗ es ↦*{de} e -∗
      ▷ (∀ (kl vl : GoSlice) (l : List (GoString × GoString)),
          R V -∗ ks ↦*{dk} k -∗ es ↦*{de} e -∗ ⌜rangeOf m k e (sint.Z limit) l⌝ -∗
          bytesListAt kl (l.map Prod.fst) -∗ bytesListAt vl (l.map Prod.snd) -∗
          Φ (PairV #kl #vl)) -∗
      WP (App (App (App (App (Val #(methods i.ty go!"UnsafeRange" i.v)) (Val #bv)) (Val #ks))
        (Val #es)) (Val #limit)) {{ Φ }}) ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (f : GoFunc)
        (I : List (GoString × GoString) → IProp GF) (J : GoInterface → IProp GF)
        (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.whole b⌝ -∗ I [] -∗
      (□ ∀ (pre : List (GoString × GoString)) (k v : GoString) (ks vs : GoSlice),
        I pre -∗ ks ↦*□ k -∗ vs ↦*□ v -∗
        WP (App (App (Val #f) (Val #ks)) (Val #vs)) {{ r, ∃ err : GoInterface, ⌜r = #err⌝ ∗
          ((⌜err = GoInterface.nil⌝ ∗ I (pre ++ [(k, v)])) ∨
           (⌜err ≠ GoInterface.nil⌝ ∗ J err)) }}) -∗
      ▷ (∀ err : GoInterface, R V -∗
          ((⌜err = GoInterface.nil⌝ ∗ ∃ l, ⌜entsOf m l⌝ ∗ I l) ∨
           (⌜err ≠ GoInterface.nil⌝ ∗ J err)) -∗ Φ #err) -∗
      WP (App (App (Val #(methods i.ty go!"UnsafeForEach" i.v)) (Val #bv)) (Val #f)) {{ Φ }}))

/-- **Ranges through `tx`** of a whole bucket of the caller's (`UnsafeRange` with an end: a batch
transaction's, or a read transaction's of a safe-range bucket only: etcd's read transactions panic on
an interval range of another bucket, `nonissues/etcd-auth-readtx-getallroles-panics.md`). -/
def txRange (tx : GoInterface) (S : Scope) (R : View → IProp GF) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tx = GoInterface.ok i⌝ ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (ks es : GoSlice) (k e : GoString)
        (dk de : DFrac) (limit : w64) (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.whole b⌝ -∗ ks ↦*{dk} k -∗ es ↦*{de} e -∗
      ▷ (∀ (kl vl : GoSlice) (l : List (GoString × GoString)),
          R V -∗ ks ↦*{dk} k -∗ es ↦*{de} e -∗ ⌜rangeOf m k e (sint.Z limit) l⌝ -∗
          bytesListAt kl (l.map Prod.fst) -∗ bytesListAt vl (l.map Prod.snd) -∗
          Φ (PairV #kl #vl)) -∗
      WP (App (App (App (App (Val #(methods i.ty go!"UnsafeRange" i.v)) (Val #bv)) (Val #ks))
        (Val #es)) (Val #limit)) {{ Φ }}))

/-- **Writing through `tx`** (the batch transaction, its lock held, the caller's view `R V` of its
scope `S`; see the header): `UnsafePut` (a key of the caller's, of an existing bucket: the bytes
read-only for good, the backend keeps them), `UnsafeDelete`, `UnsafeCreateBucket` (a whole bucket of
the caller's). -/
def txWr (tx : GoInterface) (S : Scope) (R : View → IProp GF) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tx = GoInterface.ok i⌝ ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (ks vs : GoSlice) (k v : GoString)
        (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.has b k⌝ -∗ ks ↦*□ k -∗ vs ↦*□ v -∗
      ▷ (R (V.put b k v) -∗ Φ #()) -∗
      WP (App (App (App (Val #(methods i.ty go!"UnsafePut" i.v)) (Val #bv)) (Val #ks)) (Val #vs))
        {{ Φ }}) ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (m : BData) (ks : GoSlice) (k : GoString)
        (dk : DFrac) (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜V b = some m ∧ S.has b k⌝ -∗ ks ↦*{dk} k -∗
      ▷ (R (V.del b k) -∗ ks ↦*{dk} k -∗ Φ #()) -∗
      WP (App (App (Val #(methods i.ty go!"UnsafeDelete" i.v)) (Val #bv)) (Val #ks)) {{ Φ }}) ∗
    (□ ∀ (b : Bkt) (bv : GoInterface) (V : View) (Φ : val → IProp GF),
      bucketAt b bv -∗ R V -∗ ⌜S.whole b⌝ -∗ ▷ (R (V.create b) -∗ Φ #()) -∗
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

/-- **`be`'s `Alarm` bucket holds `al`** (`none`: absent; exclusive; see the header). -/
opaque alarmBkt (be : GoInterface) (al : Option (List EtcdModel.Alarm)) : IProp GF := iprop(True)

/-- **`be`'s member buckets hold the view `st`** (exclusive; see the header). -/
opaque memberBkts (be : GoInterface) (st : Membership.ClusterSt) : IProp GF := iprop(True)

/-- (provisional, 4a's) **`be`'s `LockInsideApply` runs its post-lock hook from `Pre` to `Q`**. -/
opaque applyHook (be : GoInterface) (Pre Q : IProp GF) : IProp GF := iprop(True)

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def bucketAt_persistent.spec : Prop := ∀ b bv, Persistent (bucketAt (GF := GF) b bv)

/-- **The package's bucket variables** (the package's initialization). -/
def bucketVars_init.spec : Prop := ∀ b : Bkt,
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢
    ∃ bv, globalAddr b.var ↦□ bv ∗ bucketAt b bv

/-- **The package's key-name variables** hold their names, read-only for good (mvcc's compaction
keys among them, 3e). -/
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

/-- **A `leasepb.Lease` struct is a message holding its fields** (lent: the struct back with the
message). -/
def leaseMsg_of_struct.spec : Prop := ∀ (p : Loc) (dq : DFrac)
    (v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease),
  (p ↦{dq} v : IProp GF) ⊢ ∃ c, Proto.msgAt go_etcd_io.etcd.server.v3.lease.leasepb.Lease.ty p dq c ∗
    ⌜leaseModel c = (v.ID', v.TTL', v.RemainingTTL') ∧ c.fits ∧ Proto.marshalOk c⌝ ∗
    (Proto.msgAt go_etcd_io.etcd.server.v3.lease.leasepb.Lease.ty p dq c -∗ p ↦{dq} v)

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

end laws

end Schema
end EtcdGrove
end Perennial
