/-
# mvcc's storage contract (batch 3e): what the store needs of its backend

mvcc keeps its history in a `backend.Backend` (an interface value); **its API is stated over this
contract, not over etcd's backend** (the user, 2026-11-06: "mvcc should respect the abstractions it
builds on", `notes/decisions.md`, "mvcc's API over its storage abstraction"; PRINCIPLES, "An API is
stated over the abstractions it builds on"). etcd's backend is one storage meeting it: batch 4a
proves `keyBackend` of etcd's backend (`req/go_etcd_io_etcd_server_v3_storage_backend.md`, "from
3e"), and the server, which chooses the backend, discharges the store's storage premises through it.

## mvcc's part of a storage

`KeyData`: the part of a storage mvcc owns: the `Key` bucket (revision bytes ↦ an encoded
`mvccpb.KeyValue`) and the two compaction keys of the `Meta` bucket (`scheduledCompactRev`,
`finishedCompactRev`), and whether mvcc's two buckets exist. The storage's other buckets and `Meta`'s
other keys are its other users' (the consistent index, the lessor, auth, membership); the contract
says nothing of them.

## Vocabulary

* `MvccStorage` (opaque type): a storage's names; `storageVal B` its `backend.Backend` value;
  `kbBatchTx B` its batch transaction (the value `BatchTx()` returns, fixed), `kbReadTx B` its shared
  read transaction (`ReadTx()`'s, fixed); a bucket argument is any value `bv` with 4b's
  `Schema.bucketAt b.bkt bv` (schema's variables hold such values, `Schema.bucketVars_init`),
  `metaKey m` the compaction keys' names (4b's `schedKey`, `finKey`).
* `kbData B D` (exclusive, timeless): **mvcc's part of the storage, as a read begun now sees it, is
  `D`**. The store's invariant holds it; it changes only at a batch transaction's `Unlock` (the
  write-back: what the batch wrote becomes visible).
* `kbOpen B q` (fractional): **a share of "the storage is not closed"**: the lock rows and
  `ForceCommit` take one (etcd's backend panics on a lock-and-write or a forced commit after its
  `Close`: the hooks write through a nil bbolt transaction; 4a, "from 4a, round 1" (a)); a session
  holds it until `Unlock` gives it back. `mvccStorageFor` gives the whole, `storageRest` returns it.
* `kbLocked B q D0 D` (exclusive): **the batch transaction's lock is held (on the open share `q`),
  its session began at `D0`, and mvcc's part as the batch sees it (its own writes included) is
  `D`**. `LockInsideApply`/`LockOutsideApply` give it at the visible data (`D0 = D`); `Unlock` makes
  it visible in two steps, the session's puts at the write-back (`KeyData.mid D0 D`), then its
  deletes at the commit (4a's finding F1: a reader between them sees a compaction batch's
  `finishedCompactRev` with the batch's deleted entries still there). The `Key` delete row takes a
  key the session has not put (4a's (b): else the write-back would show the put's value, which
  `KeyData.mid` does not).
* `kbRead B rt D` (exclusive): **`rt` is a read transaction, begun, seeing `D`** (a snapshot of the
  visible data: `ConcurrentReadTx()` at its creation, the shared `ReadTx()` at its `RLock`). A
  concurrent one (`rt ≠ kbReadTx B`) sees it only up to lingering deletes (its read-buffer copy may
  predate the last commit, `nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`): its
  range row is single-key, `KeyData.linger` (4a's (e); the stale copy's fork fix is the user's open
  question 7 of batch 4a).
* `kbLive B t p` (fractional): **a share of the transaction `t`'s liveness** (the batch
  transaction's session, from a `Lock*` to its `Unlock`; a read transaction's, from its begin to its
  `RUnlock`): a range's key and value bytes are the storage's (bbolt's memory, valid while the
  transaction lives: 4c's `txBytes`), **lent against a share of it** (`rangeLent`, 4a's (f)), so
  several ranges' bytes may be out at once (`restore` hands a chunk's keys to its index goroutine
  while it reads the next; the compaction deletes the very keys its range returned) and all come
  back before the end (`Unlock`, `RUnlock` take the whole).
* `kbRdToks B n` (exclusive, counted, splits): `n` of the storage's reader slots (each begun read
  transaction holds one until its `RUnlock`; the storage's own bound on its readers, as Go's
  `RWMutex`'s reader limit: the bounds plan, the owner of the count is the storage's opener).
* `kbSafe B`, `kbSafeHeld B` (exclusive): the right to delete from the `Key` bucket, idle or held
  (`LockForSafeRangeDelete` ... `UnlockForSafeRangeDelete`: the store's compaction, one at a time).
* `kbMade B b` (persistent): mvcc's bucket `b` exists (reads and writes of a missing bucket are
  fatal in etcd's backend); `UnsafeCreateBucket` gives it.
* `storageHook B dq f` (fractional; persistent at `discard`, `hookIs B f`): a share of the storage's
  post-lock hook, at `f` (`nil`: none). `LockInsideApply` runs it under the batch lock (`hookRun B
  Pk f Pre Q`), **lending it the just-begun session** (4a's request (g), integration Y): the hook's
  triple holds for any `H` with `kbLent B H`, which it gets with `Pk ∗ Pre` and gives back with `Q`.
* `kbLent B H` (persistent): **`H` is the storage's batch session, just begun, lent to its post-lock
  hook**: what the hook may read through (the server's hook reads the shared `ReadTx()` without
  `RLock`, `cindex.go:102-110`). mvcc never opens it; the storage's implementation gives it its
  meaning (etcd's backend: `H` turns into a session `Backend.beSess γ q Fp.none S` and back,
  `MvccStorage.lean`; whose `beSess_rd` lends the read).
* `storageReq B Pk X Y` (persistent): **a forced commit turns `X` into `Y`** (the storage's commit
  runs its pre-commit hooks under the batch lock, whose invariant is `Pk`: etcd's server saves its
  consistent index there, 2d). `storageReq_true`: a commit asking nothing is always allowed.
* `kbEntryMax` (named, `2^28`): the largest entry the storage accepts (key and value bytes; 4c's
  `Bbolt.bboltEntryMax`: bbolt accepts a larger one it cannot commit or read back); both put rows
  take it (4a's (c)). Where mvcc's put gets it from is 3e's open question 2 (the size of a key and a
  value), with `proto.Marshal`'s bound.
* `keyBackend B Pk` (persistent, transparent: **the contract**): the triples of every method mvcc
  calls on the storage, its batch transaction and its read transactions, at the batch lock's
  invariant `Pk` (the client's: the hook's and the commit's resources). A bundle of an interface
  value's contracts (PRINCIPLES, "an interface value gets a bundle"), as `Schedule.isSched`.
* `mvccImage D h u` (opaque `Prop`, mvcc's own meaning): **`D` is a storage image of the history
  `h`** (its compaction revision `h.compacted`), recording an unfinished compaction iff `u` (the
  scheduled compaction key above the finished one: `restore` resumes it, so `h.compacted` is then the
  scheduled key's revision). Intended realization: the `Key` bucket holds, for each event of `h`,
  its revision's bytes (`BucketKeyToBytes`) ↦ the encoding of the key-value it wrote (a tombstone's:
  the key alone), but entries compaction removed: per key, a prefix (in revision order) of the
  revisions a compaction at `h.compacted` removes (the job deletes in revision order,
  `kvstore_compaction.go:58-92`; two jobs' prefixes are a prefix; `restoreIntoIndex` counts versions
  from the first surviving entry). With `u = false` the finished key is `h.compacted` (absent at
  `0`) and the scheduled one at most it; the removal may still be incomplete for the last batch (its
  write-back makes `finishedCompactRev` visible before its deletes, 4a's F1); with `u = true` the
  finished key is below `h.compacted`, the scheduled one; every key
  of the bucket is well formed (`BytesToRev` does not panic: `hashByRev` and `restore` parse each).
* `mvccStorageFor B Pk h u` (transparent): **the storage `B`, its batch lock's invariant `Pk`, holds
  an image of `h`, ready for a store**: what `NewStore`, `New` (3f) and `Restore` take. The contract,
  the visible data at an image of `h` (fresh: `KeyData.empty` at the empty history,
  `mvccImage_empty`), the history's receipt `⧖ (evCount h)` (mvcc's bound on its revisions: an
  execution's receipts bound every history the cluster makes, the sender's too, round 16 of the mvcc
  API; the sender's `mvccImage_obs`/`Restore`/shutdown give it, `req/..._etcdserver.md`, "from 3e"), the delete right, the store's reader slots (`mvccReaderN`, sealed) and the whole open
  share.
* `storageRest B` (transparent): what a store gives back of a storage it no longer uses (its reader
  slots, the delete right, the data, the open share): `Restore`'s old storage, and the shutdown law
  (`Api.lean`, `mvccClosed_rest`).

## Laws

`kbData_timeless`, `kbData_excl`, `kbLocked_excl`, `kbRdToks_split`, `kbMade_persistent`,
`storageReq_persistent`, `storageReq_true`, `storageHook_fractional`, `hookIs_persistent`,
`kbLent_persistent`, `kbSafe_excl`, `kbOpen_fractional`, `kbLive_fractional`, `kbRdToks_bare`,
`kbBareSlot_back`, `mvccImage_empty`, `mvccImage_reachable`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Model
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel

/-- A storage's names (opaque). -/
opaque MvccStorage : Type := Unit

/-- mvcc's two buckets. -/
inductive MBucket where
  | keyB
  | metaB

/-- The compaction keys of `Meta`. -/
inductive MetaKey where
  | sched
  | fin

section pure
variable [GooseExts]

/-- **mvcc's part of a storage** (see the header): whether its `Key` and `Meta` buckets exist, the
`Key` bucket's entries, the compaction keys' values (`none`: absent). -/
structure KeyData where
  keyMade : Bool
  metaMade : Bool
  keys : GoString → Option GoString
  sched : Option GoString
  fin : Option GoString
  /-- `true`: the storage's read buffer holds none of `Key`'s entries (all of them committed); a
  lower bound of what the storage knows: a commit keeps it, a put of `Key` clears it -/
  clean : Bool

/-- A fresh storage's: no bucket, nothing in it. -/
def KeyData.empty : KeyData := ⟨false, false, fun _ => none, none, none, true⟩

/-- An empty storage but for whether its buckets exist (a fresh member's backend: `bootstrap`
creates `Meta` before `mvcc.New`, `bootstrap.go:266`). -/
def KeyData.IsEmpty (D : KeyData) : Prop :=
  D.keys = (fun _ => none) ∧ D.sched = none ∧ D.fin = none ∧ D.clean = true

def KeyData.made (D : KeyData) : MBucket → Bool
  | .keyB => D.keyMade
  | .metaB => D.metaMade

def KeyData.create (D : KeyData) : MBucket → KeyData
  | .keyB => { D with keyMade := true }
  | .metaB => { D with metaMade := true }

def KeyData.putKey (D : KeyData) (k v : GoString) : KeyData :=
  { D with keys := fun k' => if k' = k then some v else D.keys k', clean := false }

def KeyData.delKey (D : KeyData) (k : GoString) : KeyData :=
  { D with keys := fun k' => if k' = k then none else D.keys k' }

def KeyData.getMeta (D : KeyData) : MetaKey → Option GoString
  | .sched => D.sched
  | .fin => D.fin

def KeyData.putMeta (D : KeyData) (m : MetaKey) (v : GoString) : KeyData :=
  match m with
  | .sched => { D with sched := some v }
  | .fin => { D with fin := some v }

/-- The bytes of a compaction key's name (`schema.ScheduledCompactKeyName`,
`FinishedCompactKeyName`: 4b's `Schema.schedKey`, `finKey`, `Schema.keyNames_init`). -/
def metaKey : MetaKey → GoString
  | .sched => Schema.schedKey
  | .fin => Schema.finKey

/-- The schema's bucket of mvcc's bucket (4b's `Schema.Bkt`). -/
def MBucket.bkt : MBucket → Schema.Bkt
  | .keyB => .key
  | .metaB => .metaB

/-- **A session's data at its write-back** (`batchTxBuffered.Unlock`, `batch_tx.go:330-357`): the
puts of the session over its base `D0` (its buckets, `Meta`'s keys, `Key`'s entries it has), its
deletes not yet (they become visible at the commit that follows). 4a's `Sess.mid`. -/
def KeyData.mid (D0 D : KeyData) : KeyData :=
  { D with keys := fun k => match D.keys k with
      | some v => some v
      | none => D0.keys k }

open Classical in
/-- **A backend range of a bucket's map `m`** (`UnsafeRange(bucket, k, e, limit)`): an empty `e` the
key `k` alone; else the entries of `[k, e)` in key order, cut at a positive `limit`. -/
def bkRange (m : GoString → Option GoString) (k e : GoString) (limit : Int)
    (l : List (GoString × GoString)) : Prop :=
  if e = [] then l = (match m k with | some v => [(k, v)] | none => [])
  else ∃ all : List (GoString × GoString),
    all.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧
    (∀ x, x ∈ all ↔ (go.GoStringLe k x.1 ∧ go.GoStringLt x.1 e ∧ m x.1 = some x.2)) ∧
    l = (if 0 < limit ∧ limit < all.length then all.take limit.toNat else all)

/-- mvcc's part of `Meta` as a map. -/
def KeyData.metaMap (D : KeyData) (x : GoString) : Option GoString :=
  if x = metaKey .sched then D.sched else if x = metaKey .fin then D.fin else none

/-- **What a range of mvcc's bucket `b` reads of `D` through the batch transaction** (bbolt's write
transaction holds every write: the entries in key order, cut at the limit). -/
def KeyData.range (D : KeyData) (b : MBucket) (k e : GoString) (limit : Int)
    (l : List (GoString × GoString)) : Prop :=
  match b with
  | .keyB => bkRange D.keys k e limit l
  | .metaB => bkRange D.metaMap k e limit l

open Classical in
/-- **What a range reads of `D` through a read transaction** (`baseReadTx.UnsafeRange`,
`read_tx.go:75-121`): the read buffer's entries of the range (`bs`, in key order, cut at the limit),
and, if they do not fill it, the committed entries (`cs`, cut at the limit less `bs`'s length)
followed by them: `cs.take ... ++ bs`. The buffer holds the entries put since the last commit,
above every committed one (`Key`'s keys are revisions put in increasing order: the put row's
premise), so `cs ++ bs` is the range in key order; the cut is not a prefix of it when the buffer is
not empty (bbolt's part is cut first). With `D.clean` the buffer holds none: the plain cut range.
A single-key read (`nil` end: `limit` is `1`) finds the key in either part. `Meta`'s compaction keys
are read one at a time (a `nil` end; a longer range of `Meta` panics, `read_tx.go:86`). -/
def KeyData.rtRange (D : KeyData) (b : MBucket) (k e : GoString) (limit : Int)
    (l : List (GoString × GoString)) : Prop :=
  match b with
  | .metaB => bkRange D.metaMap k e limit l
  | .keyB =>
    if e = [] then bkRange D.keys k e limit l
    else ∃ cs bs : List (GoString × GoString), bkRange D.keys k e 0 (cs ++ bs) ∧
      (D.clean = true → bs = []) ∧
      let lim : Int := if limit ≤ 0 then 2 ^ 63 - 1 else limit
      l = (if (bs.length : Int) ≥ lim then bs.take lim.toNat
           else cs.take (lim - bs.length).toNat ++ bs)

/-- **What a concurrent read transaction's single-key range reads of `D`** (4a's
`Backend.lingerSingle`): the key's entry when `D` has it; otherwise nothing, or a value it had before
a delete (the read-buffer copy taken before the last commit). -/
def KeyData.linger (D : KeyData) (b : MBucket) (k : GoString) (_e : GoString) (_limit : Int)
    (l : List (GoString × GoString)) : Prop :=
  let m := match b with | .keyB => D.keys | .metaB => D.metaMap
  l.length ≤ 1 ∧ (∀ x ∈ l, x.1 = k) ∧ (∀ v, m k = some v → l = [(k, v)])

/-- **The largest entry the storage accepts** (key and value bytes together; etcd's backend's is
bbolt's `Bbolt.bboltEntryMax`). -/
def kbEntryMax : Nat := 2 ^ 28

/-- **`D` is an image of the history `h`** (mvcc's meaning; see the header): opaque. -/
opaque mvccImage (D : KeyData) (h : KVHist) (u : Bool) : Prop

/-- **The store's reader slots** (sealed constant): how many of the storage's reader slots a store
takes (each reader of the store: a client's reader token, its own goroutines'). Its value against
the client's tokens is `Api.lean`'s `mvccReaderN_eq`; the storage's opener (4a) hands this many
over (`req/..._backend.md`, "from 3e"). -/
opaque mvccReaderN : Nat

end pure

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The storage's `backend.Backend` value.** -/
opaque storageVal (B : MvccStorage) : GoInterfaceOk :=
  interface.mk (go.GoType.StructType []) #()

/-- Its batch transaction (`BatchTx()`'s value, fixed). -/
opaque kbBatchTx (B : MvccStorage) : GoInterfaceOk :=
  interface.mk (go.GoType.StructType []) #()

/-- Its shared read transaction (`ReadTx()`'s value, fixed). -/
opaque kbReadTx (B : MvccStorage) : GoInterfaceOk :=
  interface.mk (go.GoType.StructType []) #()

/-- **mvcc's part of the storage, as a read begun now sees it, is `D`** (exclusive). -/
opaque kbData [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (D : KeyData) : IProp GF := iprop(True)

/-- **A share `q` of "the storage is not closed"** (fractional). -/
opaque kbOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (q : Qp) : IProp GF := iprop(True)

/-- **The batch lock is held on the open share `q`, its session began at mvcc's data `D0`; mvcc's
part, as the batch sees it, is `D`** (exclusive). -/
opaque kbLocked [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (q : Qp) (D0 D : KeyData) : IProp GF := iprop(True)

/-- **A share `p` of the transaction `t`'s liveness** (fractional): the storage's bytes a range of
`t` returned are lent against it (see the header). -/
opaque kbLive [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (t : GoInterfaceOk) (p : Qp) : IProp GF := iprop(True)

/-- **`rt` is a begun read transaction seeing `D`** (exclusive). -/
opaque kbRead [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (rt : GoInterfaceOk) (D : KeyData) : IProp GF := iprop(True)

/-- **`n` of the storage's reader slots** (exclusive, counted). -/
opaque kbRdToks [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (n : Nat) : IProp GF := iprop(True)

/-- The right to delete from `Key` (idle). -/
opaque kbSafe [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) : IProp GF := iprop(True)

/-- The right to delete from `Key`, the safe-range lock held. -/
opaque kbSafeHeld [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) : IProp GF := iprop(True)

/-- **This thread holds the storage's batch lock** (exclusive): what the storage's other users'
unsafe writes under the lock take (the lessor's lease-bucket delete inside a store's write
transaction, `lessor.Revoke`: 3c's provisional `beTxHeld`); `kbLocked_held` lends it. -/
opaque kbHeld [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) : IProp GF := iprop(True)

/-- **A reader slot kept for lock-only reads** (exclusive): the shared read transaction's
`RLock`/`RUnlock` with no snapshot, at any time, also after the storage's close (`kbRdToks_bare`
makes one; the opener's close takes the slots but these). -/
opaque kbBareSlot [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) : IProp GF := iprop(True)

/-- The shared read transaction locked for reading, nothing read (exclusive). -/
opaque kbBare [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) : IProp GF := iprop(True)

/-- mvcc's bucket `b` exists (persistent). -/
opaque kbMade [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (b : MBucket) : IProp GF := iprop(True)

/-- **A share `dq` of the storage's post-lock hook, at `f`** (`nil`: none). -/
opaque storageHook [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (dq : DFrac) (f : GoFunc) : IProp GF := iprop(True)

/-- **The storage's hook is `f`, for good** (its discarded share). -/
abbrev hookIs (B : MvccStorage) (f : GoFunc) : IProp GF := storageHook B DFrac.discard f

/-- **A forced commit turns `X` into `Y`** (persistent), the batch lock's invariant `Pk`. -/
opaque storageReq [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (Pk X Y : IProp GF) : IProp GF := iprop(True)

/-- **`H` is the storage's just-begun batch session, lent to its post-lock hook** (persistent; see
the header): the storage's implementation gives it its meaning. -/
opaque kbLent [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (B : MvccStorage) (H : IProp GF) : IProp GF := iprop(True)

/-- **What the post-lock hook `f` of the storage `B` does** under the batch lock of invariant `Pk`,
from the caller's `Pre`: `f`'s triple to `Q`, run holding the just-begun session (any `H` with
`kbLent B H`, given back unchanged: the hook may read through it, 4a's (g)); or with no hook, the
caller's view shift. -/
def hookRun (B : MvccStorage) (Pk : IProp GF) (f : GoFunc) (Pre Q : IProp GF) : IProp GF :=
  if f = func.nil then iprop(Pk ∗ Pre ={⊤}=∗ Q)
  else iprop(□ ∀ (H : IProp GF) (Φ : val → IProp GF), kbLent B H -∗ H ∗ Pk ∗ Pre -∗
    ▷ (H ∗ Q -∗ Φ #()) -∗ WP (App (Val #f) (Val #())) {{ Φ }})

/-- A slice of byte slices, read-only, holding `l`. -/
def bytesListAt (sl : GoSlice) (l : List GoString) : IProp GF :=
  iprop(∃ ps : List GoSlice, sl ↦*□ ps ∗ [∗list] p; b ∈ ps; l, p ↦*□ b)

/-- An atomic read of the visible data, the caller's `Φ` at it. -/
def kbObs (B : MvccStorage) (Φ : KeyData → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (D : KeyData), kbData B D }> @ ⊤, ∅ <{ kbData B D, COMM Φ D }>)

/-- **A range's result `l`, lent against `L`**: the key and value slices (owned: the storage's
fresh `append`s) of byte slices holding `l`'s keys and values at a fraction `dq` (the storage's
memory: 4c's `txBytes`), and the wand giving `L` back for those (4a's `Backend.rangeRes`; 4b's
`Schema.rangeK`). -/
def rangeLent (kl vl : GoSlice) (l : List (GoString × GoString)) (L : IProp GF) : IProp GF :=
  iprop(∃ (dq : DFrac) (ps qs : List GoSlice), kl ↦* ps ∗ vl ↦* qs ∗
    Schema.lentIn dq (l.map Prod.fst) ps ∗ Schema.lentIn dq (l.map Prod.snd) qs ∗
    (Schema.lentIn dq (l.map Prod.fst) ps -∗ Schema.lentIn dq (l.map Prod.snd) qs -∗ L))

/-- **`UnsafeRange(bk, k, e, limit)`'s triple** on a transaction `t` seeing `D` through the
resource `R` (kept), its result by `rg` (`KeyData.range` of a batch, `KeyData.rtRange` of the shared
read transaction, `KeyData.linger` of a concurrent one), its bytes lent against a share `L p` of the
transaction's liveness (`rangeLent`). An empty end is a `nil` slice (a non-`nil` empty one with no
limit panics on `Meta` and may return a `Key` entry twice, `read_tx.go:79-88`); a range of `Meta` is
of one key; with `one`, every range is of one key (a concurrent read transaction's: with an end it
may return a key twice). -/
def rangeOk (t : GoInterfaceOk) (R : IProp GF) (L : Qp → IProp GF) (D : KeyData) (one : Bool)
    (rg : KeyData → MBucket → GoString → GoString → Int → List (GoString × GoString) → Prop) :
    IProp GF :=
  iprop(□ ∀ (b : MBucket) (bv : GoInterface) (ks es : GoSlice) (k e : GoString) (dk de : DFrac)
      (limit : w64) (p : Qp) (Φ : val → IProp GF),
    Schema.bucketAt b.bkt bv -∗ R -∗ L p -∗ ks ↦*{dk} k -∗ es ↦*{de} e -∗ ⌜D.made b = true⌝ -∗
    ⌜(e = [] → es = slice.nil) ∧ (one = true → es = slice.nil) ∧
      (b = .metaB → es = slice.nil ∧ (k = metaKey .sched ∨ k = metaKey .fin))⌝ -∗
    ▷ (∀ (kl vl : GoSlice) (l : List (GoString × GoString)),
        R -∗ ks ↦*{dk} k -∗ es ↦*{de} e -∗ ⌜rg D b k e (sint.Z limit) l⌝ -∗
        rangeLent kl vl l (L p) -∗ Φ (PairV #kl #vl)) -∗
    WP (App (App (App (App (Val #(methods t.ty go!"UnsafeRange" t.v)) (Val #bv))
      (Val #ks)) (Val #es)) (Val #limit)) {{ Φ }})

/-- **The storage contract** (see the header): the triples of the methods mvcc calls. -/
def keyBackend (B : MvccStorage) (Pk : IProp GF) : IProp GF :=
  let bk := storageVal B
  let tx := kbBatchTx B
  iprop(
    -- Backend.BatchTx(), ReadTx(): the fixed transactions
    (□ ∀ Φ : val → IProp GF, ▷ Φ #(GoInterface.ok tx) -∗
      WP (App (Val #(methods bk.ty go!"BatchTx" bk.v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ Φ : val → IProp GF, ▷ Φ #(GoInterface.ok (kbReadTx B)) -∗
      WP (App (Val #(methods bk.ty go!"ReadTx" bk.v)) (Val #())) {{ Φ }}) ∗
    -- Backend.ConcurrentReadTx(): a snapshot of the visible data, at the call
    (□ ∀ (Ψ : KeyData → IProp GF) (Φ : val → IProp GF),
      kbRdToks B 1 -∗ kbObs B Ψ -∗
      ▷ (∀ (rt : GoInterfaceOk) (D : KeyData), ⌜rt ≠ kbReadTx B⌝ -∗ kbRead B rt D -∗
          kbLive B rt 1 -∗ Ψ D -∗ Φ #(GoInterface.ok rt)) -∗
      WP (App (Val #(methods bk.ty go!"ConcurrentReadTx" bk.v)) (Val #())) {{ Φ }}) ∗
    -- ReadTx.RLock(): the shared one's snapshot, at the lock; a concurrent one's, nothing
    (□ ∀ (Ψ : KeyData → IProp GF) (Φ : val → IProp GF),
      kbRdToks B 1 -∗ kbObs B Ψ -∗
      ▷ (∀ D : KeyData, kbRead B (kbReadTx B) D -∗ kbLive B (kbReadTx B) 1 -∗ Ψ D -∗ Φ #()) -∗
      WP (App (Val #(methods (kbReadTx B).ty go!"RLock" (kbReadTx B).v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ (rt : GoInterfaceOk) (D : KeyData) (Φ : val → IProp GF),
      ⌜rt ≠ kbReadTx B⌝ -∗ kbRead B rt D -∗ ▷ (kbRead B rt D -∗ Φ #()) -∗
      WP (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #())) {{ Φ }}) ∗
    -- ReadTx.RUnlock(): the reader slot back, every lent byte returned
    (□ ∀ (rt : GoInterfaceOk) (D : KeyData) (Φ : val → IProp GF),
      kbRead B rt D -∗ kbLive B rt 1 -∗ ▷ (kbRdToks B 1 -∗ Φ #()) -∗
      WP (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ Φ }}) ∗
    -- ReadTx.UnsafeRange on the shared one: of the snapshot (the read buffer's entries after
    -- bbolt's); on a concurrent one: single keys, up to lingering deletes (4a's T1)
    (□ ∀ D : KeyData,
      rangeOk (kbReadTx B) (kbRead B (kbReadTx B) D) (kbLive B (kbReadTx B)) D false
        KeyData.rtRange) ∗
    (□ ∀ (rt : GoInterfaceOk) (D : KeyData), ⌜rt ≠ kbReadTx B⌝ -∗
      rangeOk rt (kbRead B rt D) (kbLive B rt) D true KeyData.linger) ∗
    -- the shared ReadTx's RLock()/RUnlock() alone, with a slot kept for it (`kbBareSlot`): no
    -- snapshot, also after the storage's close (a mutex: the store's `Rev()`, `kv_view.go:31-35`)
    (□ ∀ Φ : val → IProp GF, kbBareSlot B -∗ ▷ (kbBare B -∗ Φ #()) -∗
      WP (App (Val #(methods (kbReadTx B).ty go!"RLock" (kbReadTx B).v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ Φ : val → IProp GF, kbBare B -∗ ▷ (kbBareSlot B -∗ Φ #()) -∗
      WP (App (Val #(methods (kbReadTx B).ty go!"RUnlock" (kbReadTx B).v)) (Val #())) {{ Φ }}) ∗
    -- BatchTx.LockInsideApply(): the batch lock (on an open share), the hook run under it
    (□ ∀ (q : Qp) (dq : DFrac) (f : GoFunc) (Pre Q : IProp GF) (Ψ : KeyData → IProp GF)
        (Φ : val → IProp GF),
      kbOpen B q -∗ storageHook B dq f -∗ Pre -∗ hookRun B Pk f Pre Q -∗ kbObs B Ψ -∗
      ▷ (∀ D : KeyData, storageHook B dq f -∗ Q -∗ kbLocked B q D D -∗ kbLive B tx 1 -∗ Ψ D -∗
          Φ #()) -∗
      WP (App (Val #(methods tx.ty go!"LockInsideApply" tx.v)) (Val #())) {{ Φ }}) ∗
    -- BatchTx.LockOutsideApply(): the batch lock (on an open share), no hook
    (□ ∀ (q : Qp) (Ψ : KeyData → IProp GF) (Φ : val → IProp GF),
      kbOpen B q -∗ kbObs B Ψ -∗
      ▷ (∀ D : KeyData, Pk -∗ kbLocked B q D D -∗ kbLive B tx 1 -∗ Ψ D -∗ Φ #()) -∗
      WP (App (Val #(methods tx.ty go!"LockOutsideApply" tx.v)) (Val #())) {{ Φ }}) ∗
    -- BatchTx.Unlock(): every lent byte back; the batch's data made visible in two steps (it may
    -- commit, under `Pk`): its puts at the write-back (`KeyData.mid`), then its deletes at the
    -- commit that follows (`batch_tx.go:330-357`; a session without deletes: the second changes
    -- nothing, but is still the caller's update to give); the open share back
    (□ ∀ (q : Qp) (D0 D : KeyData) (Ψ : IProp GF) (Φ : val → IProp GF),
      kbLocked B q D0 D -∗ kbLive B tx 1 -∗ Pk -∗
      (AU <{ ∃∃ (D1 : KeyData), kbData B D1 }> @ ⊤, ∅ <{ kbData B (KeyData.mid D0 D), COMM
        AU <{ ∃∃ (D2 : KeyData), kbData B D2 }> @ ⊤, ∅ <{ kbData B D, COMM Ψ }> }>) -∗
      ▷ (kbOpen B q -∗ Ψ -∗ Φ #()) -∗
      WP (App (Val #(methods tx.ty go!"Unlock" tx.v)) (Val #())) {{ Φ }}) ∗
    -- BatchTx.UnsafeCreateBucket(b)
    (□ ∀ (b : MBucket) (bv : GoInterface) (q : Qp) (D0 D : KeyData) (Φ : val → IProp GF),
      Schema.bucketAt b.bkt bv -∗ kbLocked B q D0 D -∗
      ▷ (kbLocked B q D0 (D.create b) -∗ kbMade B b -∗ Φ #()) -∗
      WP (App (Val #(methods tx.ty go!"UnsafeCreateBucket" tx.v)) (Val #bv)) {{ Φ }}) ∗
    -- BatchTx.UnsafePut / UnsafeSeqPut of `Key` (read-only bytes: the storage may keep them)
    -- (the key above every key the session began with or has: 4a's `Sess.fresh`; an entry the
    -- storage accepts: 4a's (c))
    (□ ∀ (m : GoString) (bv : GoInterface) (q : Qp) (D0 D : KeyData) (ks vs : GoSlice)
        (k v : GoString) (Φ : val → IProp GF),
      ⌜m = go!"UnsafePut" ∨ m = go!"UnsafeSeqPut"⌝ -∗ Schema.bucketAt .key bv -∗
      kbLocked B q D0 D -∗
      ⌜D.keyMade = true ∧ k.length + v.length ≤ kbEntryMax ∧
        ∀ k' v', (D0.keys k' = some v' ∨ D.keys k' = some v') → go.GoStringLt k' k⌝ -∗
      ks ↦*□ k -∗ vs ↦*□ v -∗
      ▷ (kbLocked B q D0 (D.putKey k v) -∗ Φ #()) -∗
      WP (App (App (App (Val #(methods tx.ty m tx.v)) (Val #bv)) (Val #ks)) (Val #vs))
        {{ Φ }}) ∗
    -- BatchTx.UnsafePut of a compaction key of `Meta`
    (□ ∀ (mk : MetaKey) (bv : GoInterface) (q : Qp) (D0 D : KeyData) (ks vs : GoSlice)
        (v : GoString) (Φ : val → IProp GF),
      Schema.bucketAt .metaB bv -∗
      kbLocked B q D0 D -∗ ⌜D.metaMade = true ∧ (metaKey mk).length + v.length ≤ kbEntryMax⌝ -∗
      ks ↦*□ metaKey mk -∗ vs ↦*□ v -∗
      ▷ (kbLocked B q D0 (D.putMeta mk v) -∗ Φ #()) -∗
      WP (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #bv))
        (Val #ks)) (Val #vs)) {{ Φ }}) ∗
    -- BatchTx.UnsafeDelete of `Key`: the safe-range lock held; a key this session has not put
    -- (4a's (b): mvcc's compaction deletes revisions committed before its session)
    (□ ∀ (bv : GoInterface) (q : Qp) (D0 D : KeyData) (ks : GoSlice) (k : GoString) (dk : DFrac)
        (Φ : val → IProp GF),
      Schema.bucketAt .key bv -∗
      kbLocked B q D0 D -∗ kbSafeHeld B -∗ ⌜D.keyMade = true ∧ D.keys k = D0.keys k⌝ -∗
      ks ↦*{dk} k -∗
      ▷ (kbLocked B q D0 (D.delKey k) -∗ kbSafeHeld B -∗ ks ↦*{dk} k -∗ Φ #()) -∗
      WP (App (App (Val #(methods tx.ty go!"UnsafeDelete" tx.v)) (Val #bv)) (Val #ks))
        {{ Φ }}) ∗
    -- BatchTx.UnsafeRange: of the batch's data, its bytes lent against the session's liveness
    (□ ∀ (q : Qp) (D0 D : KeyData),
      rangeOk tx (kbLocked B q D0 D) (kbLive B tx) D false KeyData.range) ∗
    -- Backend.ForceCommit(): the client's commit request (on an open share)
    (□ ∀ (q : Qp) (X Y : IProp GF) (Φ : val → IProp GF),
      kbOpen B q -∗ X -∗ storageReq B Pk X Y -∗ ▷ (kbOpen B q -∗ Y -∗ Φ #()) -∗
      WP (App (Val #(methods bk.ty go!"ForceCommit" bk.v)) (Val #())) {{ Φ }}) ∗
    -- Backend.LockForSafeRangeDelete(), UnlockForSafeRangeDelete()
    (□ ∀ Φ : val → IProp GF, kbSafe B -∗ ▷ (kbSafeHeld B -∗ Φ #()) -∗
      WP (App (Val #(methods bk.ty go!"LockForSafeRangeDelete" bk.v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ Φ : val → IProp GF, kbSafeHeld B -∗ ▷ (kbSafe B -∗ Φ #()) -∗
      WP (App (Val #(methods bk.ty go!"UnlockForSafeRangeDelete" bk.v)) (Val #())) {{ Φ }}) ∗
    -- Backend.Size(), SizeInUse(), OpenReadTxN(): any `int64`, at any time
    (□ ∀ (m : GoString) (Φ : val → IProp GF),
      ⌜m = go!"Size" ∨ m = go!"SizeInUse" ∨
        m = go!"OpenReadTxN"⌝ -∗ ▷ (∀ n : w64, Φ #n) -∗
      WP (App (Val #(methods bk.ty m bk.v)) (Val #())) {{ Φ }}))

/-- **The storage `B` holds an image of `h`, ready for a store** (see the header): its read buffer
holds none of `Key`'s entries (`D.clean`: an opened storage's, and `NewStore`'s own commit before
`restore`'s chunked scan); each bucket that exists, known to. -/
def mvccStorageFor (B : MvccStorage) (Pk : IProp GF) (h : KVHist) (u : Bool) : IProp GF :=
  iprop(keyBackend B Pk ∗ (∃ D : KeyData, kbData B D ∗ ⌜mvccImage D h u ∧ D.clean = true⌝ ∗
      (⌜D.keyMade = true⌝ -∗ kbMade B .keyB) ∗ (⌜D.metaMade = true⌝ -∗ kbMade B .metaB)) ∗
    ⧖ (evCount h) ∗ kbSafe B ∗ kbRdToks B mvccReaderN ∗ kbOpen B 1)

/-- **What a store gives back of a storage it no longer uses**: its data, the delete right, `n`
reader slots (all of them, `mvccReaderN`, but those kept for lock-only reads) and the whole open
share. -/
def storageRest (B : MvccStorage) (n : Nat) : IProp GF :=
  iprop((∃ D : KeyData, kbData B D) ∗ kbSafe B ∗ kbRdToks B n ∗ kbOpen B 1)

end vocab

/-! ## Laws (obligations of the storage's implementation, and of mvcc for `mvccImage`) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def kbData_timeless.spec : Prop := ∀ B D, Timeless (kbData (GF := GF) B D)

def kbData_excl.spec : Prop := ∀ B D D', kbData (GF := GF) B D ∗ kbData B D' ⊢ iprop(False)

def kbLocked_excl.spec : Prop := ∀ B q q' D0 D D0' D',
  kbLocked (GF := GF) B q D0 D ∗ kbLocked B q' D0' D' ⊢ iprop(False)

def kbSafe_excl.spec : Prop := ∀ B, kbSafe (GF := GF) B ∗ kbSafeHeld B ⊢ iprop(False)

def kbOpen_fractional.spec : Prop := ∀ B, Fractional (fun q => kbOpen (GF := GF) B q)

def kbLive_fractional.spec : Prop := ∀ B t, Fractional (fun p => kbLive (GF := GF) B t p)

/-- The batch lock's holder may lend "the lock is held" to the storage's other users (their writes
under it leave mvcc's part alone: 4a's `writable` over cells no one tracks), with the session's
liveness (no range's bytes out then: the schema's write bundle's view holds it, 4a's `btView`;
integration Y). -/
def kbLocked_held.spec : Prop := ∀ B q D0 D,
  kbLocked (GF := GF) B q D0 D ∗ kbLive B (kbBatchTx B) 1 ⊢
    kbHeld B ∗ (kbHeld B -∗ kbLocked B q D0 D ∗ kbLive B (kbBatchTx B) 1)

def kbRdToks_split.spec : Prop := ∀ B n m,
  kbRdToks (GF := GF) B (n + m) ⊣⊢ kbRdToks B n ∗ kbRdToks B m

def kbMade_persistent.spec : Prop := ∀ B b, Persistent (kbMade (GF := GF) B b)

/-- A reader slot kept for lock-only reads (the opener's close then waits only for its mutex). -/
def kbRdToks_bare.spec : Prop := ∀ B, kbRdToks (GF := GF) B 1 ={⊤}=∗ kbBareSlot B

/-- **An idle lock-only slot is a reader slot again** (the store's `Restore` hands the `Rev` pool's
slots of the old storage back with the rest, `storageRest B mvccReaderN`: no `Rev` runs then, it
holds `s.mu`). -/
def kbBareSlot_back.spec : Prop := ∀ B, kbBareSlot (GF := GF) B ={⊤}=∗ kbRdToks B 1

def kbLent_persistent.spec : Prop := ∀ B (H : IProp GF), Persistent (kbLent B H)

def storageReq_persistent.spec : Prop := ∀ B (Pk X Y : IProp GF), Persistent (storageReq B Pk X Y)

/-- A commit asking nothing. -/
def storageReq_true.spec : Prop := ∀ B (Pk : IProp GF), ⊢ storageReq B Pk iprop(True) iprop(True)

def storageHook_fractional.spec : Prop := ∀ B f,
  Fractional (fun q => storageHook (GF := GF) B (DFrac.own q) f)

def hookIs_persistent.spec : Prop := ∀ B f, Persistent (hookIs (GF := GF) B f)

/-- Two shares of the hook agree. -/
def storageHook_agree.spec : Prop := ∀ B dq dq' f f',
  storageHook (GF := GF) B dq f ∗ storageHook B dq' f' ⊢ ⌜f = f'⌝

def keyBackend_persistent.spec : Prop := ∀ B (Pk : IProp GF), Persistent (keyBackend B Pk)

/-- **An empty storage is an image of the empty history** (whichever of mvcc's buckets exist: a
fresh member's backend has `Meta` already, `bootstrap.go:266`). -/
def mvccImage_empty.spec : Prop := ∀ D : KeyData, D.IsEmpty → mvccImage D ⟨[], 0⟩ false

/-- **An image's history is reachable** (a history a store went through: the image facts that travel
with a snapshot or a disk carry it, in place of a premise no caller could establish). -/
def mvccImage_reachable.spec : Prop := ∀ D h u, mvccImage D h u → MvccReachable ⟨h, []⟩

end laws

end Mvcc
end EtcdGrove
end Perennial
