/-
# etcd's storage backend (`server/storage/backend`): the vocabulary (batch 4a)

The backend is a bbolt database (4c) with one long-lived **batch transaction** (bbolt's write
transaction, committed periodically, `batch_tx.go`), a **read buffer** holding the writes since the
last commit (`tx_buffer.go`), and **read transactions** that read the last commit's bbolt read
transaction with the read buffer over it (`read_tx.go`). Its clients are many and own disjoint parts
of one database: mvcc (the `key` bucket, `meta`'s compaction keys), the consistent index and the
hooks (`meta`'s index, term and configuration), the lessor (`lease`), auth (three buckets),
membership, alarms, the schema's version. So the vocabulary is **one image, owned by footprints**.

## The model (transparent)

* `Image`: the database as etcd sees it: which top-level buckets exist (`made`) and their entries
  (`ents b k`; no nested buckets: etcd makes none). The operations `create`, `put`, `del`,
  `dropBkt`. bbolt's `Data` (4c's `Model.lean`) maps onto it (`imgOf`, in the realization).
* `Cell` (a bucket's existence, or one key of a bucket) and footprints `Fp := Cell → Prop`
  (`Fp.all`, `Fp.none`, `Fp.bucket b`, `Fp.key b k`, `Fp.union`); `Image.agree F I J`: `I` and `J`
  agree on `F`.
* `Sess`: **a batch session** (the batch lock held, from a `Lock*` to its `Unlock`): the image
  visible when it began (`base`), the batch's image now (`cur`), and the last value it put at each key
  (`puts`). `Sess.mid`: what readers see between the session's write-back and its commit: its puts
  over `base` (the read buffer gets the puts at the write-back; a delete reaches the readers only
  with the commit, which `Unlock` makes when the session deleted anything:
  `batchTxBuffered.Unlock`, `batch_tx.go:328-360`, etcd-io/etcd#17119). `Sess.fresh S b k`: `k` is
  above every key of `b` the session sees or began with (a sequential bucket's write-back keeps the
  buffer sorted only so: `txWriteBuffer.writeback` sorts only buckets written by `UnsafePut`).
* `sortedEnts`, `btRange` (a batch transaction's range: bbolt's write cursor, in key order, cut at a
  positive limit) and `rdRange` (a read transaction's: the read buffer's part of the range is cut
  first and returned after bbolt's, `read_tx.go:75-121`: with the split between the two hidden, a
  safe-range bucket's result is `A.take m ++ B.take n` for a split `all = A ++ B` of the range, a
  single key is found in either; other buckets are read one entry at a time). `rdOrder`: a read
  transaction's `ForEach` order (bbolt's entries not in the buffer, then the buffer's).
* `BktInfo`: a bucket value's name, id and whether it is a safe-range bucket.

## The resources (opaque unless marked)

* `isBackend γ b p Pk` (persistent): **`b` is a `*backend` with names `γ`, over the database file
  at `p`, whose batch lock protects the client's `Pk`** (the commit hooks' and the commit's
  resources: `hookOk`, `commitOk`, fixed at `New`). Intended realization: the backend's fields
  read-only; `batchTx.Mutex`'s lock invariant (the batch session's authority: bbolt's write
  transaction `boltTx` (4c) and the write buffer at `cur`, the pending counters, `Pk`), `readTx.mu`'s
  (the read buffer and bbolt's read transaction at the visible image; the authorities of `beVis`),
  `txReadBufferCache.mu`'s, `safeRangeDeleteMu`'s, `mu`'s (the `bolt.DB`, `isBolt`, and `boltState`
  of 4c: its committed data the last element of the history `beHist`), the run loop's channels, the
  hooks' contract, `envOk`.
* `beOpen γ q` (fractional): the backend is not closed; a session, a commit, a snapshot and a
  defragmentation hold a share; `Close` takes all of it.
* `beCur γ F C` (exclusive per footprint, splits): **the batch image on `F` is `C`** (the current
  data: what the next batch session begins with, and what the next commit makes durable).
  Client-owned: each client holds its cells; writes need it and a session.
* `beVis γ F V` (exclusive per footprint, splits, timeless): **what a read transaction begun now
  sees on `F` is `V`**. Client-owned (TaDa): it changes only by the client's atomic updates, which
  `Unlock` (and a commit, for the hooks' cells) fire. A client that never reads `F` through read
  transactions gives it up for good (`beVis_drop`: `beNoVis γ F`, persistent), and may then write
  `F` in other clients' sessions (the lessor's delete in mvcc's write transaction).
* `beSess γ q F S` (exclusive): **this thread holds the batch lock, in session `S`, publishing the
  cells `F`** at its `Unlock` (the visible-image updates of `F`; `F` may grow, `beSess_widen`).
  Lendable whole: a callee writing under its caller's session (the lessor under mvcc's) takes it
  and gives it back.
* `beTurn γ` (exclusive, timeless; verify-round, A10-provability B1): **the batch lock's turn**:
  every `Lock*` returns it with the session, and `Unlock`'s second update takes it back at its
  commit point (the lock's invariant holds it between sessions). A client that parks lock-scoped
  state between sessions (mvcc's storage bridge takes its batch part out at the lock and puts it back
  at the second update) parks the turn with it; a new session's turn refutes a stale parked case
  (`beTurn_excl`): no session begins before the previous one's second update fired.
* `beCurIs γ I` (exclusive, ephemeral): the whole batch image is `I`: what a commit hands its
  client's commit step (`commitOk`, `beReq`) to compare with the parts it holds.
* `beHist γ L` (exclusive, timeless; client-owned): **the images committed (or attempted) so far, in
  order; the file holds the last; a crash leaves one of them** (bbolt's `BoltSt.recovers`, with
  `UnsafeNoFsync` off). Each commit appends the batch image by the client's update (`commitOk`).
  `beCommitted γ I` (persistent): `I` is in the history. `beFinal γ I` (persistent): the backend is
  closed, `I` its last commit. `beHistLb γ L` (persistent; verify-round, A10-completeness F1): the
  history has the prefix `L` (a lower bound: what `Snapshot` takes, to return an image at least as
  new as `L`'s last).
* `beRdToks γ n` (counted, splits): `n` reader slots (a read transaction's: the read lock and the
  interval's wait group; a snapshot's and a hash's bbolt read transaction). `New` gives
  `beReaderN` of them (sealed); the backend's close does not take them back (in-flight readers
  finish first: `Close` waits for them through bbolt's `mmaplock`).
* `beRd γ rt F V` (exclusive): a begun read transaction `rt` (a `*concurrentReadTx`, or the shared
  `*readTx` while read-locked) seeing `V` on `F`; the shared one exactly, a concurrent one up to
  lingering deletes (its buffer copy may predate the last commit: `lingerSingle`, `rdOrderL`).
* `beLive γ t p` (fractional): **a share of the transaction `t`'s liveness** (`btLoc γ`: the batch
  session, from a `Lock*` to its `Unlock`; `rtLoc γ` or a concurrent one's `l`: from its begin to
  its `RUnlock`). A range's key and value bytes are bbolt's memory (or the read buffer's), valid
  while the transaction lives (4c's `txBytes`): **lent against a share of it** (`rangeRes`), the
  transaction's own resource (`beSess`, `beRd`) kept, so several ranges' bytes may be out at once
  and the session may write meanwhile (mvcc's compaction deletes the very keys its range returned;
  its `restore` hands a chunk's keys to a goroutine while reading the next); all come back before
  the end (`Unlock`, `RUnlock` take the whole).
* `beHook γ dq f` (fractional; `discard` persistent): the post-lock hook is `f` (`nil`: none).
* `beDel γ`, `beDelHeld γ` (exclusive): the right to delete from a safe-range bucket, idle or
  held (`LockForSafeRangeDelete`: excludes a non-blocking defragmentation, which would otherwise
  copy the deleted keys back).
* `beMade γ b` (persistent): bucket `b` exists, for good (`beCur_freeze`: its existence cell given
  up); creating it again is a no-op.
* `beSnapN γ s I n` (exclusive): an open snapshot `s` of the committed image `I`, of size `n`; each
  `WriteTo` writes some bytes `bs` of `I` of that length (`imgBytes I bs`, `bs.length = n`): not the
  same bytes each time (bbolt's `Tx.WriteTo` reads the free pages below the high-water mark from the
  file, which a concurrent commit may rewrite: A11-completeness F5).
* `beFile p o` (exclusive, timeless): the closed database file at `p` holds `o` (`none`: no file,
  or an empty one). Intended realization: the file's OsFs resources, every byte clean and durable,
  an image of `D` with `imgOf D = I` (4c's `fileHolds p D` when its name is durable, its premise but
  for the name otherwise: `Bbolt.boltReopen_alloc` opens it); for `none`, `boltFresh_alloc`'s
  premise. **Its name may not be durable** (second crash pass, G-a: a file `bolt.Open` created in
  this generation, whose directory nothing synced since): the revert state says so. `beRevs p os`
  (exclusive; second pass, a list at the re-review): the files a crash may bring back at `p`, renamed
  over and not yet synced, and `none` while a file created here has no durable name (`[]`:
  `beNoRevert p`; else `beRevertL p os`; `beRevert`, `beRev` transitional one-file forms;
  `Durable.lean`). Realization: 4a's per-path ghost record of `p`'s pending name states, its
  authority in the file's invariant (`beFileN`) with OsFs's name state of `p` (`osMeta`'s `named`)
  and the previous inodes' contents, keeping `named = false → none ∈ os` for a file of an image.
  The open's update (`beOpenUpd`) takes both and, opening a `none` file (bbolt creates it, no
  directory sync: `nonissues/bbolt-create-dir-not-synced.md`), adds `none` to the list; a directory
  sync (`SaveDBFrom`'s, the same directory `member/snap`) clears it.
* `beDetached γ p` (exclusive; second crash pass, G-b): **the open backend `γ`'s file was renamed
  over at `p`** (etcd's `applySnapshot` installs the snapshot's file while the old backend is open,
  `server.go:1068` vs `:1144`): its bytes stay reachable through the open handle until its `Close`,
  and a crash before a directory sync may bring it back at `p` at any committed image of its
  history. Given by the rename's update over the open form (`beAt p (.opened γ L)`,
  `beRenamedOver`), taken by the old backend's close (`beCloseUpd`'s detached form, which puts the
  final image into the revert list) or, at a crash, by `Durable.lean`'s `beDetached_crash`.
* `bucketOk bk bi` (transparent, persistent): `bk`'s methods `ID()`, `Name()`,
  `IsSafeRangeBucket()` return `bi` (4b proves it of `Schema.bucketAt`).
* `envOk` (persistent): **the program-start environment**: `ETCD_VERIFY` unset (the lock checks and
  `verify` asserts are off); `envOk_intro` from `etcdVerifyUnset`. (Threads: the run loop takes
  `New`'s caller's `threadTok`, which `Close` returns; each commit's rollback goroutine is forked
  with the token the rolled-back read transaction held, `wp_fork_tok_self`, the new read
  transaction getting the forking thread's fresh one; a snapshot's monitor with the snapshot's.)
* `beBkt γ bi` (persistent): `bi` is one of the buckets `New`'s caller declared (`bktsOk`: distinct
  ids); `bkt γ bk bi` (transparent) = `bucketOk bk bi ∗ beBkt γ bi`, every read and write's bucket.
* `beHookFp γ Fh` (persistent): the pre-commit hooks write only `Fh` (puts); a concurrent read
  transaction reads only footprints disjoint from it, and a read-transaction range of a safe-range
  bucket only one with no `Fh` cell.
* `beSynced γ` (persistent, `UnsafeNoFsync` off), `beDurInv γ p` (persistent: the file's crash
  invariant): the crash law (`Durable.lean`).
* **The file moves between the client's crash state and the backend's at two atomic steps**
  (repair3-boot, the crash pass's requests 1 and 2): the client keeps the file's crash state in an
  invariant (outside `beFileN`, the namespace of the backend's file invariants), closed
  (`beFile p o`) or open (`beDurInv γ p ∗ beSynced γ ∗ beHist γ L`), with its revert state
  `beRevs p os` beside it throughout. `New` takes the closed file through the update `beOpenUpd`,
  fired at bbolt's open (4c's `fileHolds_alloc` and 4a's allocation of the history: a ghost step), which
  puts the open file's crash state in its place; `Close` gives it back through `beCloseUpd`, fired
  at the release after bbolt's `DB.Close` (4c's `boltRelease`), which takes the history and puts the
  closed file in its place. So at every point a crash finds one of the two forms in the client's
  invariant: `beFile_crash` or `beCrash` applies (4c's `Open` and `DB.Close` keep the file in
  `boltFile`'s crash invariant throughout, closed or open).
* `dbOpenOk cfg` (opaque `Prop`): **the environment premise**: bbolt's `Open` of `cfg.Path` with
  the backend's options succeeds (the file is a bbolt database or absent, the lock is free or
  `Timeout` is zero, the mmap of `MmapSize` succeeds). `newBackend` panics otherwise.
* Contracts (transparent): `hookOk γ hk Fh Pk` (the pre-commit hooks' triple, puts of `Fh` only, `hookWrites`; `hookFnOk` of a
  `HookFunc`), `commitOk γ Pk` (the
  client's commit step), `beReq γ Pk X Y` (a forced commit's per-call step), `hookRun γ q Pk f Pre Q`
  (the post-lock hook's triple), `visitOk` (a `ForEach` visitor, keeping the bytes `lentAll` it is
  lent until the caller gives them back for the transaction's liveness), `writeOk` (an `io.Writer`),
  `ignOk` (`Hash`'s filter); `lentIn`/`rangeRes` (a range's bytes, lent against a share of
  the transaction's liveness `beLive`), `lingerSingle`/`rdOrderL` (a concurrent read's), `covers`, `writable`, `beNew` (what `New` hands its
  client's allocation step).

## Laws

`isBackend_persistent`, `beOpen_fractional`, `beCur_split`, `beCur_excl`, `beCur_agree`,
`beVis_split`, `beVis_agree`, `beVis_none`, `beVis_timeless`, `beVis_drop`, `beNoVis_persistent`,
`beNoVis_mono`, `beNoVis_excl`, `beSess_excl`, `beSess_widen`, `beSess_cur`, `beSess_vis`, `beSess_rd`, `beTurn_excl`, `beTurn_timeless`,
`beCurIs_cur`, `beCurIs_vis`, `beCurIs_flush`, `beHist_timeless`,
`beHist_mem`, `beHist_final`, `beHist_lb`, `beHist_lb_prefix`, `beHistLb_persistent`, `beHistLb_mono`,
`beHistLb_nil`, `beCommitted_persistent`, `beFinal_persistent`, `beFinal_cur`,
`beRdToks_split`, `beLive_fractional`, `beReaderN_ge`, `beHook_fractional`, `beHook_agree`, `beHook_persistent`, `beDel_excl`,
`beCur_freeze`, `beMade_persistent`, `beMade_cur`, `beFile_timeless`, `beFile_excl`, `beDetached_excl`
(second crash pass, G-b),
`beBkt_{persistent, inj}`, `beHookFp_persistent`, `beSynced_persistent`, `beDurInv_persistent`,
`safeRegOk_persistent`, `envOk_{persistent, intro}`, `imgBytes_size`, `beReq_true`, `beReq_persistent`.

## Requirement snippets

`examples/specreq/backend/`: `parts.go` (`ReqWriteThenRead`: a session's puts visible after
`Unlock`; `ReqDeleteVisible`; `ReqLentWrite`: an untracked write under another client's session;
`ReqBareRLock`), `commit.go` (`ReqForceCommitDurable`, `ReqReopen`: a closed backend's file reopened
holds the last commit; `ReqHookWrites`), `snapshot.go` (`ReqSnapshotStream`), `ranges.go`
(`ReqSeqRange`: a safe-range bucket's limited read; `ReqMetaSingle`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.storage.backend
public import Spec.go_etcd_io.bbolt.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

/-- A backend's ghost names (opaque). -/
opaque BeNames : Type := Unit

/-! ## The model -/

section model
variable [GooseExts]

/-- **The database as etcd sees it**: which top-level buckets exist and their entries; and, in a
visible image only, for each bucket whether **the read buffer surely holds none of its entries but
the pre-commit hooks' leftovers** (`clean`: a lower bound, kept by commits, which empty the buffer,
and cleared by a written-back put; the hooks' puts stay in the write buffer after their commit and
reach the read buffer at a later write-back, at the committed values; meaningless in a batch or
committed image). -/
structure Image where
  made : GoString → Bool
  ents : GoString → GoString → Option GoString
  clean : GoString → Bool

/-- A fresh database: no bucket (bbolt's `init`). -/
def Image.empty : Image := ⟨fun _ => false, fun _ _ => none, fun _ => true⟩

/-- The image with every bucket clean (the visible image of a just-opened backend, or at a
commit). -/
def Image.flushed (I : Image) : Image := { I with clean := fun _ => true }

def Image.create (I : Image) (b : GoString) : Image :=
  { I with made := fun b' => if b' = b then true else I.made b' }

def Image.put (I : Image) (b k v : GoString) : Image :=
  { I with ents := fun b' k' => if b' = b ∧ k' = k then some v else I.ents b' k' }

def Image.del (I : Image) (b k : GoString) : Image :=
  { I with ents := fun b' k' => if b' = b ∧ k' = k then none else I.ents b' k' }

/-- The bucket `b` deleted with its entries (no-op if absent: `ErrBucketNotFound` is ignored). -/
def Image.dropBkt (I : Image) (b : GoString) : Image :=
  { I with made := fun b' => if b' = b then false else I.made b',
           ents := fun b' k' => if b' = b then none else I.ents b' k' }

/-- A cell of the database: a bucket's existence, one key of a bucket, or (visible images only)
whether the read buffer holds none of a bucket's entries. -/
inductive Cell where
  | bkt (b : GoString)
  | key (b k : GoString)
  | buf (b : GoString)

/-- A footprint: a set of cells. -/
abbrev Fp := Cell → Prop

def Fp.all : Fp := fun _ => True
def Fp.none : Fp := fun _ => False
def Fp.union (F G : Fp) : Fp := fun c => F c ∨ G c
/-- A bucket's existence, all its keys and its buffer flag. -/
def Fp.bucket (b : GoString) : Fp := fun c => c = .bkt b ∨ c = .buf b ∨ ∃ k, c = .key b k
/-- One key. -/
def Fp.key (b k : GoString) : Fp := fun c => c = .key b k
/-- A bucket's existence alone. -/
def Fp.bkt (b : GoString) : Fp := fun c => c = .bkt b

/-- `I` and `J` agree on `F`'s data cells (existence and entries). -/
def Image.agree (F : Fp) (I J : Image) : Prop :=
  ∀ b, (F (.bkt b) → I.made b = J.made b) ∧ ∀ k, F (.key b k) → I.ents b k = J.ents b k

/-- Two visible images agree on `F`: its data cells and its buffer flags. -/
def Image.agreeV (F : Fp) (I J : Image) : Prop :=
  Image.agree F I J ∧ ∀ b, F (.buf b) → I.clean b = J.clean b

/-- **A batch session** (see the header). -/
structure Sess where
  base : Image
  cur : Image
  puts : GoString → GoString → Option GoString

/-- A session begun at the image `I` (the visible image is the batch's between sessions). -/
def Sess.init (I : Image) : Sess := ⟨I, I, fun _ _ => none⟩

/-- The session put to bucket `b`. -/
def Sess.putIn (S : Sess) (b : GoString) : Prop := ∃ k v, S.puts b k = some v

open Classical in
/-- **What readers see between the session's write-back and its commit**: its puts over `base`;
a bucket it put to no longer known clean. -/
def Sess.mid (S : Sess) : Image :=
  ⟨S.cur.made, fun b k => match S.puts b k with | some v => some v | none => S.base.ents b k,
   fun b => S.base.clean b && !(decide (S.putIn b))⟩

/-- **What readers see after the session**: the batch image, with `mid`'s buffer flags (a commit
empties the buffer, but `Unlock` commits only when it must: the flags stay a lower bound). -/
def Sess.fin (S : Sess) : Image := { S.cur with clean := S.mid.clean }

def Sess.put (S : Sess) (b k v : GoString) : Sess :=
  { S with cur := S.cur.put b k v,
           puts := fun b' k' => if b' = b ∧ k' = k then some v else S.puts b' k' }

def Sess.del (S : Sess) (b k : GoString) : Sess := { S with cur := S.cur.del b k }

def Sess.create (S : Sess) (b : GoString) : Sess := { S with cur := S.cur.create b }

def Sess.dropBkt (S : Sess) (b : GoString) : Sess := { S with cur := S.cur.dropBkt b }

/-- `k` is above every key of `b` the session sees or began with. -/
def Sess.fresh (S : Sess) (b k : GoString) : Prop :=
  ∀ k', ((S.base.ents b k').isSome ∨ (S.cur.ents b k').isSome) → go.GoStringLt k' k

/-- The entries of `L` in `[k, e)`, in key order. -/
def sortedEnts (L : GoString → Option GoString) (k e : GoString)
    (all : List (GoString × GoString)) : Prop :=
  all.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧
  ∀ x, x ∈ all ↔ (go.GoStringLe k x.1 ∧ go.GoStringLt x.1 e ∧ L x.1 = some x.2)

/-- The key `k` alone, if present. -/
def single (L : GoString → Option GoString) (k : GoString) : List (GoString × GoString) :=
  match L k with
  | some v => [(k, v)]
  | none => []

/-- **A batch transaction's range** (`unsafeRange` over bbolt's write cursor): an empty end the key
alone; else the range in key order, cut at a positive `limit`. -/
def btRange (L : GoString → Option GoString) (k e : GoString) (limit : Int)
    (l : List (GoString × GoString)) : Prop :=
  if e = [] then l = single L k
  else ∃ all, sortedEnts L k e all ∧
    l = (if 0 < limit ∧ limit < all.length then all.take limit.toNat else all)

/-- **A read transaction's range** (`baseReadTx.UnsafeRange`): an empty end the key alone (found
in the buffer or in bbolt); a safe-range bucket's range split, unknown to the reader, into bbolt's
part `A` and the buffer's `B` (the buffer's keys above bbolt's: the put rows' premise; `B` empty if
the bucket is known clean), the buffer's cut first (`n`) and returned last; any other bucket's at
most one entry of the range, none only if the range is empty (`limit` is `1` there: the triple's
premise). -/
def rdRange (L : GoString → Option GoString) (safe clean : Bool) (k e : GoString) (limit : Int)
    (l : List (GoString × GoString)) : Prop :=
  if e = [] then l = single L k
  else if safe then
    ∃ all j, sortedEnts L k e all ∧ (clean = true → j = all.length) ∧
      let A := all.take j
      let B := all.drop j
      let n := if 0 < limit then min limit.toNat B.length else B.length
      let m := if 0 < limit then limit.toNat - n else A.length
      l = A.take m ++ B.take n
  else
    l.length ≤ 1 ∧
    (∀ x ∈ l, go.GoStringLe k x.1 ∧ go.GoStringLt x.1 e ∧ L x.1 = some x.2) ∧
    (l = [] → ∀ x v, go.GoStringLe k x → go.GoStringLt x e → L x ≠ some v)

/-- **A read transaction's `ForEach` order**: every entry once, as two runs in key order (bbolt's
entries the buffer does not shadow, then the buffer's). -/
def rdOrder (L : GoString → Option GoString) (l : List (GoString × GoString)) : Prop :=
  ∃ A B, l = A ++ B ∧ A.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧
    B.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧ (l.map Prod.fst).Nodup ∧
    ∀ x, x ∈ l ↔ L x.1 = some x.2

/-- A batch transaction's `ForEach` order: the bucket's entries in key order. -/
def btOrder (L : GoString → Option GoString) (l : List (GoString × GoString)) : Prop :=
  l.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧ ∀ x, x ∈ l ↔ L x.1 = some x.2

/-- **A concurrent read transaction's single-key read** (`concurrentReadTx.UnsafeRange` with a `nil`
end): the key's value in `L` when `L` has it; otherwise nothing, or a value the key had before a
delete. A concurrent read transaction may lay a read-buffer copy taken before the last commit over
the bbolt transaction of after it (`txReadBufferCache` keyed by the buffer version, which a commit
does not bump: `nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`): what the copy holds
of a key the commit deleted, the reader still sees. -/
def lingerSingle (L : GoString → Option GoString) (k : GoString) (l : List (GoString × GoString)) :
    Prop :=
  l.length ≤ 1 ∧ (∀ x ∈ l, x.1 = k) ∧ (∀ v, L k = some v → l = [(k, v)])

/-- **A concurrent read transaction's `ForEach` order**: every entry of `L` once, and possibly
entries at keys `L` lacks (see `lingerSingle`), each key once. -/
def rdOrderL (L : GoString → Option GoString) (l : List (GoString × GoString)) : Prop :=
  (l.map Prod.fst).Nodup ∧ (∀ k v, L k = some v → (k, v) ∈ l) ∧
    ∀ x ∈ l, L x.1 = some x.2 ∨ L x.1 = none

/-- Two footprints are disjoint. -/
def Fp.disj (F G : Fp) : Prop := ∀ c, ¬ (F c ∧ G c)

/-- A read of `[k, e)` (`e = []`: the key `k`) of bucket `b` stays within `F`. -/
def covers (F : Fp) (b k e : GoString) : Prop :=
  if e = [] then F (.key b k) else ∀ x, F (.key b x)

/-- **A bucket value's identity** (`ID()`, `Name()`, `IsSafeRangeBucket()`). -/
structure BktInfo where
  name : GoString
  id : w64
  safe : Bool

/-- **`bs` are the bytes of a database file whose image is `I`** (bbolt's `Tx.WriteTo`; opaque:
4c's file format). -/
opaque imgBytes (I : Image) (bs : List w8) : Prop

/-- **The backend's reader slots** (sealed constant): how many `New` gives. -/
opaque beReaderN : Nat

/-- **An entry lent to a `ForEach` visitor**: its key and value, the slices holding them and the
fraction (bbolt's memory, or the read buffer's; 4b's `Schema.LentKV`). -/
structure Lent where
  k : GoString
  v : GoString
  ks : GoSlice
  vs : GoSlice
  dq : DFrac

def Lent.ent (x : Lent) : GoString × GoString := (x.k, x.v)

end model

/-! ## The resources -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `b` as a `Backend` value. -/
def beIface (b : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b

/-- The batch transaction of the backend `γ` (`b.batchTx`, a `*batchTxBuffered`; fixed). -/
opaque btLoc (γ : BeNames) : Loc

/-- The shared read transaction of the backend `γ` (`b.readTx`, a `*readTx`; fixed). -/
opaque rtLoc (γ : BeNames) : Loc

/-- The batch transaction as a `BatchTx` (and `UnsafeReadWriter`) value. -/
def btIface (γ : BeNames) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty)
    #(btLoc γ)

/-- The shared read transaction as a `ReadTx` value. -/
def rtIface (γ : BeNames) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty)
    #(rtLoc γ)

/-- A `*concurrentReadTx` as a `ReadTx` value. -/
def crtIface (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty)
    #l

/-- **`b` is a backend `γ` over the file at `p`, its batch lock protecting `Pk`** (persistent). -/
opaque isBackend [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) : IProp GF := iprop(True)

/-- The backend is not closed (fractional). -/
opaque beOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (q : Qp) : IProp GF := iprop(True)

/-- **The batch image on `F` is `C`** (exclusive per footprint). -/
opaque beCur [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (F : Fp) (C : Image) : IProp GF := iprop(True)

/-- **What a read transaction begun now sees on `F` is `V`** (exclusive per footprint). -/
opaque beVis [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (F : Fp) (V : Image) : IProp GF := iprop(True)

/-- `F`'s visible image is tracked by no client, for good (persistent). -/
opaque beNoVis [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (F : Fp) : IProp GF := iprop(True)

/-- **This thread holds the batch lock, in session `S`, publishing `F`** (exclusive). -/
opaque beSess [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) : IProp GF := iprop(True)

/-- **The batch lock's turn** (exclusive; see the header). -/
opaque beTurn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) : IProp GF := iprop(True)

/-- The whole batch image is `I` (ephemeral: lent at a commit). -/
opaque beCurIs [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (I : Image) : IProp GF := iprop(True)

/-- **The committed (or attempted) images so far, in order** (client-owned). -/
opaque beHist [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (L : List Image) : IProp GF := iprop(True)

/-- **The history has the prefix `L`** (persistent, monotone). -/
opaque beHistLb [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (L : List Image) : IProp GF := iprop(True)

/-- `I` was committed (persistent). -/
opaque beCommitted [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (I : Image) : IProp GF := iprop(True)

/-- The backend is closed, `I` its last commit (persistent). -/
opaque beFinal [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (I : Image) : IProp GF := iprop(True)

/-- `n` reader slots (counted). -/
opaque beRdToks [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (n : Nat) : IProp GF := iprop(True)

/-- A begun read transaction `rt` seeing `V` on `F` (exclusive). -/
opaque beRd [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (rt : Loc) (F : Fp) (V : Image) : IProp GF := iprop(True)

/-- **A share `p` of the transaction `t`'s liveness** (fractional; see the header). -/
opaque beLive [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (t : Loc) (p : Qp) : IProp GF := iprop(True)

/-- A share `dq` of the post-lock hook, at `f` (`nil`: none). -/
opaque beHook [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (dq : DFrac) (f : GoFunc) : IProp GF := iprop(True)

/-- The right to delete from a safe-range bucket (idle). -/
opaque beDel [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) : IProp GF := iprop(True)

/-- The right to delete from a safe-range bucket, the safe-range lock held. -/
opaque beDelHeld [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) : IProp GF := iprop(True)

/-- Bucket `b` exists for good (persistent). -/
opaque beMade [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (b : GoString) : IProp GF := iprop(True)

/-- **An open snapshot `s` of the committed image `I`, of size `n`** (exclusive): each `WriteTo`
writes some bytes of `I` of length `n` (see the header). -/
opaque beSnapN [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (s : Loc) (I : Image) (n : Nat) : IProp GF := iprop(True)

/-- **The closed database file at `p` holds `o`** (`none`: no file; exclusive). -/
opaque beFile [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : GoString) (o : Option Image) : IProp GF := iprop(True)

/-- **Renames onto `p` await a directory sync; a crash may bring back any of the previous files,
which held `os`** (exclusive; meaningful for a non-empty `os`; `Durable.lean`'s header). -/
opaque beRevertL [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : GoString) (os : List (Option Image)) : IProp GF := iprop(True)

/-- **The open backend `γ`'s file was renamed over at `p`** (exclusive; second crash pass, G-b; see
the header). -/
opaque beDetached [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (p : GoString) : IProp GF := iprop(True)

/-- **No rename onto `p` awaits a directory sync** (exclusive). -/
opaque beNoRevert [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : GoString) : IProp GF := iprop(True)

/-- **`p`'s revert state as the list of the files a crash may bring back** (re-review N3): `[]`,
no rename pending (`beNoRevert`); else `beRevertL`. -/
def beRevs (p : GoString) : List (Option Image) → IProp GF
  | [] => beNoRevert p
  | os => beRevertL p os

/-- (transitional: server-boot's `snap/Api.lean` names it) one pending rename over a file that held
`o`: `beRevs p [o]`. -/
def beRevert (p : GoString) (o : Option Image) : IProp GF := beRevertL p [o]

/-- (transitional: rafthttp's `saveOk` names it) the revert state of at most one pending rename:
`beRevs p rv.toList`. -/
def beRev (p : GoString) (rv : Option (Option Image)) : IProp GF := beRevs p rv.toList

/-- **`bk` is a `Bucket` value with identity `bi`** (transparent, persistent): the bundle of the
three methods the backend calls (`ID()`, `Name()` (a read-only slice), `IsSafeRangeBucket()`), as an
interface value's bundle; the schema proves it of its bucket variables (4b's `Schema.bucketAt`). -/
def bucketOk (bk : GoInterface) (bi : BktInfo) : IProp GF :=
  match bk with
  | .nil => iprop(False)
  | .ok i =>
    iprop((□ ∀ Φ : val → IProp GF, ▷ Φ #bi.id -∗
        WP (App (Val #(methods i.ty go!"ID" i.v)) (Val #())) {{ Φ }}) ∗
      (□ ∀ Φ : val → IProp GF, ▷ (∀ sl : GoSlice, sl ↦*□ bi.name -∗ Φ #sl) -∗
        WP (App (Val #(methods i.ty go!"Name" i.v)) (Val #())) {{ Φ }}) ∗
      (□ ∀ Φ : val → IProp GF, ▷ Φ #bi.safe -∗
        WP (App (Val #(methods i.ty go!"IsSafeRangeBucket" i.v)) (Val #())) {{ Φ }}))

/-- **`bi` is one of the backend's buckets** (persistent): one of the set `New`'s caller declares,
whose ids are distinct (the read buffer is keyed by id). -/
opaque beBkt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (bi : BktInfo) : IProp GF := iprop(True)

/-- A bucket value of this backend. -/
def bkt (γ : BeNames) (bk : GoInterface) (bi : BktInfo) : IProp GF :=
  iprop(bucketOk bk bi ∗ beBkt γ bi)

/-- **The pre-commit hooks write only the cells `Fh`** (persistent; fixed at `New`). -/
opaque beHookFp [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (Fh : Fp) : IProp GF := iprop(True)

/-- **Crash safety is on** (persistent: `New` with `UnsafeNoFsync` off): the history's crash
meaning holds (`Durable.lean`'s `beCrash`). -/
opaque beSynced [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) : IProp GF := iprop(True)

/-- **The crash invariant of the backend's file `p`** (persistent; realized by 4c's `boltFile`). -/
opaque beDurInv [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (p : GoString) : IProp GF := iprop(True)

/-- **The state of the file at `p` a rename onto `p` replaces** (second crash pass, G-b): closed,
holding `o` (`beFile p o`), or the open backend `γ`'s, of history `L` (`beDurInv γ p ∗ beHist γ L`:
the old backend still commits through the client's `commitOk`, so the update gives its history
back). -/
inductive FileSt where
  | closed (o : Option Image)
  | opened (γ : BeNames) (L : List Image)

/-- The client's crash state of `p` in the form `d`. -/
def beAt (p : GoString) : FileSt → IProp GF
  | .closed o => beFile p o
  | .opened γ L => iprop(beDurInv γ p ∗ beHist γ L)

/-- **What a rename onto `p` leaves of the replaced file `d`** (second crash pass, G-b): a closed
file joins the revert list (`o :: os`); an open one keeps its history and is detached
(`beDetached γ p`: its entry joins the list when it closes, `beCloseUpd`, or at a crash,
`beDetached_crash`). -/
def beRenamedOver (p : GoString) (os : List (Option Image)) : FileSt → IProp GF
  | .closed o => beRevs p (o :: os)
  | .opened γ L => iprop(beDurInv γ p ∗ beHist γ L ∗ beDetached γ p ∗ beRevs p os)


/-- **The safe-range registry names only safe-range buckets** (persistent; `safeRangeBucketNames`,
filled by the schema's initialization, `schema/bucket.go:64`): what a non-blocking defragmentation's
catch-up needs. Introduction: the schema's initialization (4b; a recorded gap). -/
opaque safeRegOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] : IProp GF := iprop(True)

/-- **The program-start environment** (persistent; see the header). -/
opaque envOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] : IProp GF := iprop(True)

/-- **Byte slices lent at the fraction `dq`**: the slices `ps` holding `l` (4b's `Schema.lentIn`). -/
def lentIn (dq : DFrac) (l : List GoString) (ps : List GoSlice) : IProp GF :=
  iprop([∗list] p; b ∈ ps; l, p ↦*{dq} b)

/-- **A slice of byte slices holding `l`**, each at the fraction `dq` (the read buffer's internal
ranges: the session's put bytes, read-only for good). -/
def bytesListAt (sl : GoSlice) (l : List GoString) (dq : DFrac) : IProp GF :=
  iprop(∃ ps : List GoSlice, sl ↦* ps ∗ [∗list] p; b ∈ ps; l, p ↦*{dq} b)

/-- **A range's result `l`, lent against `L`** (a share of the transaction's liveness,
`beLive`): the key and value slices (owned: fresh `append`s) of byte slices holding `l` at a
fraction `dq` (bbolt's, or the read buffer's: 4c's `txBytes`, readable while the transaction
lives), and the wand giving `L` back for the inner slices. -/
def rangeRes (kl vl : GoSlice) (l : List (GoString × GoString)) (L : IProp GF) : IProp GF :=
  iprop(∃ (dq : DFrac) (ps qs : List GoSlice), kl ↦* ps ∗ vl ↦* qs ∗
    lentIn dq (l.map Prod.fst) ps ∗ lentIn dq (l.map Prod.snd) qs ∗
    (lentIn dq (l.map Prod.fst) ps -∗ lentIn dq (l.map Prod.snd) qs -∗ L))

/-- **A cell set a session may write**: published by the session (`F`), or tracked by no one. -/
def writable (γ : BeNames) (F G : Fp) : IProp GF :=
  iprop(⌜∀ c, G c → F c⌝ ∨ beNoVis γ G)

/-- **The client's commit step** (persistent): at a commit, holding `Pk` and the whole batch image
`I`, the client appends `I` to its history (and gets `Pk` back). -/
def commitOk (γ : BeNames) (Pk : IProp GF) : IProp GF :=
  iprop(□ ∀ I : Image, Pk -∗ beCurIs γ I -∗
    AU <{ ∃∃ (L : List Image), beHist γ L }> @ ⊤, ∅ <{ beHist γ (L ++ [I]), COMM Pk ∗ beCurIs γ I }>)

/-- **What a pre-commit hook may leave**: a session whose writes are puts of cells of `Fh` only
(no delete: the commit makes the puts visible at once; no other cell changed). -/
def hookWrites (Fh : Fp) (S S' : Sess) : Prop :=
  S'.base = S.base ∧ (∀ c, ¬ Fh c → Image.agree (fun c' => c' = c) S'.cur S.cur) ∧
    (∀ b k v, S'.puts b k = some v → Fh (.key b k)) ∧
    (∀ b k, Fh (.key b k) → S'.cur.ents b k = none → S.cur.ents b k = none)

/-- **The pre-commit hooks' contract** (`nil`: no hooks): `OnPreCommitUnsafe(tx)`, run by a commit
holding the batch lock (`Pk` and a session at the batch image, whose base is what readers see then:
the enclosing `Unlock`'s `Sess.mid`), puts cells of `Fh` and hands the commit the update of those it
publishes, to fire when the commit makes them visible. -/
def hookOk (γ : BeNames) (hk : GoInterface) (Fh : Fp) (Pk : IProp GF) : IProp GF :=
  match hk with
  | .nil => iprop(True)
  | .ok h =>
    iprop(□ ∀ (q : Qp) (S : Sess) (Φ : val → IProp GF),
      Pk -∗ beSess γ q Fp.none S -∗
      ▷ (∀ (F : Fp) (S' : Sess) (Ψ : IProp GF), ⌜hookWrites Fh S S' ∧ ∀ c, F c → Fh c⌝ -∗
          beSess γ q F S' -∗
          (AU <{ ∃∃ (V : Image), beVis γ F V }> @ ⊤, ∅ <{ beVis γ F S'.fin, COMM Ψ }>) -∗
          (Ψ -∗ Pk) -∗ Φ #()) -∗
      WP (App (Val #(methods h.ty go!"OnPreCommitUnsafe" h.v)) (Val #(btIface γ))) {{ Φ }})

/-- **A `HookFunc`'s contract** (`NewHooks`'s argument): `hookOk`'s, for the function itself. -/
def hookFnOk (γ : BeNames) (f : GoFunc) (Fh : Fp) (Pk : IProp GF) : IProp GF :=
  iprop(□ ∀ (q : Qp) (S : Sess) (Φ : val → IProp GF),
    Pk -∗ beSess γ q Fp.none S -∗
    ▷ (∀ (F : Fp) (S' : Sess) (Ψ : IProp GF), ⌜hookWrites Fh S S' ∧ ∀ c, F c → Fh c⌝ -∗
        beSess γ q F S' -∗
        (AU <{ ∃∃ (V : Image), beVis γ F V }> @ ⊤, ∅ <{ beVis γ F S'.fin, COMM Ψ }>) -∗
        (Ψ -∗ Pk) -∗ Φ #()) -∗
    WP (App (Val #f) (Val #(btIface γ))) {{ Φ }})

/-- **A forced commit's per-call step**: at the commit, holding `Pk`, the caller's `X` and the
committed whole image `I`, give `Pk` back and get `Y` (persistent). -/
def beReq (γ : BeNames) (Pk X Y : IProp GF) : IProp GF :=
  iprop(□ ∀ I : Image, Pk -∗ X -∗ beCurIs γ I -∗ beCommitted γ I -∗ |={⊤}=> Pk ∗ beCurIs γ I ∗ Y)

/-- **What the post-lock hook `f` does** under the batch lock of resource `Pk`, from the caller's
`Pre`: `f`'s triple to `Q`, run holding the just-begun session (`q`, nothing published), which it
may lend to a read of the shared read transaction without `RLock` (`beSess_rd`: the server's hook
reads the consistent index so, `cindex.go:102-110`) and gives back unchanged; or with no hook, the
caller's view shift. -/
def hookRun (γ : BeNames) (q : Qp) (Pk : IProp GF) (f : GoFunc) (Pre Q : IProp GF) : IProp GF :=
  if f = func.nil then iprop(Pk ∗ Pre ={⊤}=∗ Q)
  else iprop(□ ∀ (S : Sess) (Φ : val → IProp GF), beSess γ q Fp.none S ∗ Pk ∗ Pre -∗
    ▷ (beSess γ q Fp.none S ∗ Q -∗ Φ #()) -∗ WP (App (Val #f) (Val #())) {{ Φ }})

/-- **The bytes lent to a visitor so far** (`Lent`s). -/
def lentAll (l : List Lent) : IProp GF :=
  iprop([∗list] x ∈ l, x.ks ↦*{x.dq} x.k ∗ x.vs ↦*{x.dq} x.v)

/-- **A `ForEach` visitor's contract** over the caller's state `P done` (the entries visited so far,
with the slices lent to it: integration Y, I6's finding): a call on key and value bytes (bbolt's, or
the buffer's) either succeeds, **keeping them** in `P` (`unsafeGetAllUsers` appends the value slices
and unmarshals them after the loop: 4b's `Schema.txRd`), or fails with its own error `err`, giving
them back, its state `E done err` (the `ForEach` returns that very error). -/
def visitOk (vis : GoFunc) (P : List Lent → IProp GF) (E : List Lent → GoInterface → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (done : List Lent) (ks vs : GoSlice) (k v : GoString) (dq : DFrac) (Φ : val → IProp GF),
    P done -∗ ks ↦*{dq} k -∗ vs ↦*{dq} v -∗
    ▷ (∀ err : GoInterface,
        ((⌜err = interface.nil⌝ ∗ P (done ++ [⟨k, v, ks, vs, dq⟩])) ∨
         (⌜err ≠ interface.nil⌝ ∗ ks ↦*{dq} k ∗ vs ↦*{dq} v ∗ E done err)) -∗ Φ #err) -∗
    WP (App (App (Val #vis) (Val #ks)) (Val #vs)) {{ Φ }})

/-- **An `io.Writer`'s contract** over the caller's record `W` of the bytes written so far. -/
def writeOk (w : GoInterface) (W : List w8 → IProp GF) : IProp GF :=
  match w with
  | .nil => iprop(False)
  | .ok wi =>
    iprop(□ ∀ (pre bs : List w8) (sl : GoSlice) (dq : DFrac) (Φ : val → IProp GF),
      W pre -∗ sl ↦*{dq} bs -∗
      ▷ (∀ (n : w64) (err : GoInterface), sl ↦*{dq} bs -∗
          ((⌜err = interface.nil ∧ uint.nat n = bs.length⌝ ∗ W (pre ++ bs)) ∨
           (⌜err ≠ interface.nil⌝ ∗ ∃ j, ⌜j ≤ bs.length⌝ ∗ W (pre ++ bs.take j))) -∗
          Φ (PairV #n #err)) -∗
      WP (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #sl)) {{ Φ }})

/-- **`Hash`'s filter's contract**: `ignores(bucket, key)` returns on any bytes. -/
def ignOk (ign : GoFunc) : IProp GF :=
  iprop(⌜ign = func.nil⌝ ∨
    □ ∀ (bs ks : GoSlice) (b k : GoString) (Φ : val → IProp GF),
      bs ↦*□ b -∗ ks ↦*□ k -∗ ▷ (∀ r : Bool, Φ #r) -∗
      WP (App (App (Val #ign) (Val #bs)) (Val #ks)) {{ Φ }})

/-- **A declared bucket set**: distinct ids, one identity per name. -/
def bktsOk (Bs : BktInfo → Prop) : Prop :=
  ∀ a b, Bs a → Bs b → (a.id = b.id ∨ a.name = b.name) → a = b

/-- **What `New` hands its client's allocation step**: the whole image (batch and visible), the
reader slots, the open token, the hook (none), the delete right. (repair3-boot: the history
`beHist γ [I]` is no longer here: `beOpenUpd`'s commit puts it in the client's crash state.) -/
def beNew (γ : BeNames) (I : Image) : IProp GF :=
  iprop(beCur γ Fp.all I ∗ beVis γ Fp.all I.flushed ∗ beRdToks γ beReaderN ∗
    beOpen γ 1 ∗ beHook γ (DFrac.own 1) func.nil ∗ beDel γ)

/-- **The namespace of the backend's file invariants** (4c's `boltFile`, 4a's history authority):
the masks of `beOpenUpd`/`beCloseUpd` leave it to the backend. -/
def beFileN : Namespace := nroot .@ "etcdBackendFile"

/-- **The open's update** (repair3-boot, the crash pass's request 1): fired by `New` at bbolt's
open, a ghost step; takes the closed file at `p` holding `o` out of the client's crash state and
puts the open file's in its place: its crash invariant, crash safety (with `UnsafeNoFsync` off),
the history at the file's image. `R γ` is the client's, handed to its allocation step. A client
with no invariant builds it from `beFile p o ∗ beRevs p os` it owns (`R γ` then holds what the commit
gives). Changes (second crash pass, G-a): it also takes the revert state and, for `o = none` (bbolt
creates the file, with no directory sync), gives it back with `none` added: until a sync of the
directory a crash may leave no file, also after `Close` (`beFile_crash`'s `o' ∈ os`), where
`beFile_crash` claimed the file survives. -/
def beOpenUpd (p : GoString) (o : Option Image) (ns : Bool) (R : BeNames → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (os : List (Option Image)), beFile p o ∗ beRevs p os }> @ ⊤ \ ↑beFileN, ∅
    <{ ∀∀ (γ : BeNames), beDurInv γ p ∗ (if ns then iprop(True) else beSynced γ) ∗
        beHist γ [o.getD Image.empty] ∗
        beRevs p (match o with
          | none => none :: os
          | some _ => os), COMM R γ }>)

/-- **The close's update** (repair3-boot, the crash pass's request 2): fired by `Close` at the
release after bbolt's `DB.Close`; takes the history out of the client's crash state and puts the
closed file, at its last image, in its place. `Q I` is the client's, returned by `Close`. Changes
(second crash pass, G-b): a **detached** file (`d = some os`: renamed over while open, `beDetached γ
p`; `applySnapshot`'s old backend) is no longer named `p`, so its close gives no `beFile p`: its
final image joins `p`'s revert list (`some I :: os`, the file a crash before a directory sync may
bring back). -/
def beCloseUpd (γ : BeNames) (p : GoString) (Q : Image → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (L : List Image) (d : Option (List (Option Image))), beHist γ L ∗
        (match d with
         | none => iprop(emp)
         | some os => iprop(beDetached γ p ∗ beRevs p os)) }> @ ⊤ \ ↑beFileN, ∅
    <{ ∀∀ (I : Image), ⌜L.getLast? = some I⌝ ∗
        (match d with
         | none => beFile p (some I)
         | some os => beRevs p (some I :: os)), COMM Q I }>)

end vocab

/-- **`ETCD_VERIFY` is unset for the whole run** (a program-start fact; 2e's `backendEnvOk`). -/
opaque etcdVerifyUnset : Prop

/-- **The environment premise** for opening the file (see the header). -/
opaque dbOpenOk [GooseExts] (cfg : go_etcd_io.etcd.server.v3.storage.backend.BackendConfig) : Prop

/-! ## Laws (obligations of the backend's implementation) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def isBackend_persistent.spec : Prop := ∀ γ b p (Pk : IProp GF), Persistent (isBackend γ b p Pk)

/-- One backend has one name and one file (the schema's wrappers hide `γ`: 4b's `alarmBkt`,
`memberBkts`, `applyHook` are over the `Backend` value only). -/
def isBackend_agree.spec : Prop := ∀ γ γ' b p p' (Pk Pk' : IProp GF),
  isBackend γ b p Pk ∗ isBackend γ' b p' Pk' ⊢ ⌜γ = γ' ∧ p = p'⌝

def beOpen_fractional.spec : Prop := ∀ γ (q₁ q₂ : Qp),
  beOpen (GF := GF) γ (q₁ + q₂) ⊣⊢ beOpen γ q₁ ∗ beOpen γ q₂

/-- A part splits along disjoint footprints (and joins back). -/
def beCur_split.spec : Prop := ∀ γ (F G : Fp) C, (∀ c, ¬ (F c ∧ G c)) →
  (beCur (GF := GF) γ (Fp.union F G) C ⊣⊢ beCur γ F C ∗ beCur γ G C)

def beCur_excl.spec : Prop := ∀ γ (F G : Fp) C C',
  beCur (GF := GF) γ F C ∗ beCur γ G C' ⊢ ⌜∀ c, ¬ (F c ∧ G c)⌝

/-- Only the footprint's cells matter. -/
def beCur_agree.spec : Prop := ∀ γ F C C', Image.agree F C C' →
  (beCur (GF := GF) γ F C ⊢ beCur γ F C')

def beVis_split.spec : Prop := ∀ γ (F G : Fp) V, (∀ c, ¬ (F c ∧ G c)) →
  (beVis (GF := GF) γ (Fp.union F G) V ⊣⊢ beVis γ F V ∗ beVis γ G V)

def beVis_agree.spec : Prop := ∀ γ F V V', Image.agreeV F V V' →
  (beVis (GF := GF) γ F V ⊢ beVis γ F V')

/-- Tracking nothing is free. -/
def beVis_none.spec : Prop := ∀ γ V, ⊢ beVis (GF := GF) γ Fp.none V

def beVis_timeless.spec : Prop := ∀ γ F V, Timeless (beVis (GF := GF) γ F V)

/-- Give up tracking `F` for good. -/
def beVis_drop.spec : Prop := ∀ γ F V, beVis (GF := GF) γ F V ==∗ beNoVis γ F

def beNoVis_persistent.spec : Prop := ∀ γ F, Persistent (beNoVis (GF := GF) γ F)

def beNoVis_mono.spec : Prop := ∀ γ (F G : Fp), (∀ c, G c → F c) →
  (beNoVis (GF := GF) γ F ⊢ beNoVis γ G)

/-- Tracked and untracked cells are disjoint. -/
def beNoVis_excl.spec : Prop := ∀ γ (F G : Fp) V,
  beNoVis (GF := GF) γ F ∗ beVis γ G V ⊢ ⌜∀ c, ¬ (F c ∧ G c)⌝

/-- One session at a time. -/
def beSess_excl.spec : Prop := ∀ γ q q' F F' S S',
  beSess (GF := GF) γ q F S ∗ beSess γ q' F' S' ⊢ iprop(False)

/-- A session may promise to publish more cells. -/
def beSess_widen.spec : Prop := ∀ γ q (F G : Fp) S,
  beSess (GF := GF) γ q F S ⊢ beSess γ q (Fp.union F G) S

/-- The session's batch image agrees with every part. -/
def beSess_cur.spec : Prop := ∀ γ q F S G C,
  beSess (GF := GF) γ q F S ∗ beCur γ G C ⊢ ⌜Image.agree G S.cur C⌝

/-- During a session, every tracked cell is visible at the session's base (a session begun by a
`Lock*` at the batch image; a hook's, inside a commit, at what readers then see). -/
def beSess_vis.spec : Prop := ∀ γ q F S G V,
  beSess (GF := GF) γ q F S ∗ beVis γ G V ⊢ ⌜Image.agreeV G S.base V⌝

/-- **The shared read transaction read without `RLock` under the batch lock** (the post-lock hook's
`UnsafeConsistentIndex`, `cindex.go:107`): the lock excludes the read buffer's writers (the
write-back, the commit), so the session lends a read of the visible image, with no slot. -/
def beSess_rd.spec : Prop := ∀ γ q F S G V,
  beSess (GF := GF) γ q F S ∗ beVis γ G V ⊢
    beRd γ (rtLoc γ) G V ∗ beLive γ (rtLoc γ) 1 ∗
    (beRd γ (rtLoc γ) G V -∗ beLive γ (rtLoc γ) 1 -∗ beSess γ q F S ∗ beVis γ G V)

/-- **One turn at a time** (the lock's invariant holds it between sessions). -/
def beTurn_excl.spec : Prop := ∀ γ, beTurn (GF := GF) γ ∗ beTurn γ ⊢ iprop(False)

def beTurn_timeless.spec : Prop := ∀ γ, Timeless (beTurn (GF := GF) γ)

def beCurIs_cur.spec : Prop := ∀ γ I G C,
  beCurIs (GF := GF) γ I ∗ beCur γ G C ⊢ ⌜Image.agree G I C⌝

/-- At a commit point (where `beCurIs` is lent), every tracked cell's entries are the batch
image's. -/
def beCurIs_vis.spec : Prop := ∀ γ I G V,
  beCurIs (GF := GF) γ I ∗ beVis γ G V ⊢ ⌜Image.agree G I V⌝

/-- **At a commit point the read buffer is empty**: a tracker may record its buckets clean. -/
def beCurIs_flush.spec : Prop := ∀ γ I G V,
  beCurIs (GF := GF) γ I ∗ beVis γ G V ==∗ beCurIs γ I ∗ beVis γ G V.flushed

def beHist_timeless.spec : Prop := ∀ γ L, Timeless (beHist (GF := GF) γ L)

def beHist_mem.spec : Prop := ∀ γ L I, beHist (GF := GF) γ L ∗ beCommitted γ I ⊢ ⌜I ∈ L⌝

def beHist_final.spec : Prop := ∀ γ L I, beHist (GF := GF) γ L ∗ beFinal γ I ⊢ ⌜L.getLast? = some I⌝

/-- The history's lower bound, taken from the history (the client's). -/
def beHist_lb.spec : Prop := ∀ γ L, beHist (GF := GF) γ L ⊢ beHistLb γ L

def beHist_lb_prefix.spec : Prop := ∀ γ L L0,
  beHist (GF := GF) γ L ∗ beHistLb γ L0 ⊢ ⌜L0 <+: L⌝

def beHistLb_persistent.spec : Prop := ∀ γ L, Persistent (beHistLb (GF := GF) γ L)

def beHistLb_mono.spec : Prop := ∀ γ (L0 L : List Image), L0 <+: L →
  (beHistLb (GF := GF) γ L ⊢ beHistLb γ L0)

def beHistLb_nil.spec : Prop := ∀ γ, ⊢ beHistLb (GF := GF) γ []

def beCommitted_persistent.spec : Prop := ∀ γ I, Persistent (beCommitted (GF := GF) γ I)

def beFinal_persistent.spec : Prop := ∀ γ I, Persistent (beFinal (GF := GF) γ I)

/-- A closed backend's last image is every part's batch image. -/
def beFinal_cur.spec : Prop := ∀ γ I G C,
  beFinal (GF := GF) γ I ∗ beCur γ G C ⊢ ⌜Image.agree G I C⌝

def beLive_fractional.spec : Prop := ∀ γ t, Fractional (fun p => beLive (GF := GF) γ t p)

def beRdToks_split.spec : Prop := ∀ γ n m,
  beRdToks (GF := GF) γ (n + m) ⊣⊢ beRdToks γ n ∗ beRdToks γ m

/-- Room for every client's readers (mvcc's, auth's, the server's). -/
def beReaderN_ge.spec : Prop := 2 ^ 28 ≤ beReaderN

def beHook_fractional.spec : Prop := ∀ γ f,
  Fractional (fun q => beHook (GF := GF) γ (DFrac.own q) f)

def beHook_agree.spec : Prop := ∀ γ dq dq' f f',
  beHook (GF := GF) γ dq f ∗ beHook γ dq' f' ⊢ ⌜f = f'⌝

def beHook_persistent.spec : Prop := ∀ γ f, Persistent (beHook (GF := GF) γ DFrac.discard f)

def beDel_excl.spec : Prop := ∀ γ, beDel (GF := GF) γ ∗ beDelHeld γ ⊢ iprop(False)

/-- An existing bucket's existence cell given up: it exists for good. -/
def beCur_freeze.spec : Prop := ∀ γ b C, C.made b = true →
  (beCur (GF := GF) γ (Fp.bkt b) C ==∗ beMade γ b)

def beMade_persistent.spec : Prop := ∀ γ b, Persistent (beMade (GF := GF) γ b)

def beMade_cur.spec : Prop := ∀ γ q F S b,
  beSess (GF := GF) γ q F S ∗ beMade γ b ⊢ ⌜S.cur.made b = true⌝

def beFile_timeless.spec : Prop := ∀ p o, Timeless (beFile (GF := GF) p o)

def beFile_excl.spec : Prop := ∀ p o o', beFile (GF := GF) p o ∗ beFile p o' ⊢ iprop(False)

/-- One detached file per backend and path (second crash pass, G-b). -/
def beDetached_excl.spec : Prop := ∀ γ p, beDetached (GF := GF) γ p ∗ beDetached γ p ⊢ iprop(False)

def beBkt_persistent.spec : Prop := ∀ γ bi, Persistent (beBkt (GF := GF) γ bi)

/-- The backend's buckets have distinct ids (the read buffer is keyed by id). -/
def beBkt_inj.spec : Prop := ∀ γ bi bi',
  beBkt (GF := GF) γ bi ∗ beBkt γ bi' ⊢ ⌜bi.id = bi'.id → bi = bi'⌝

def beHookFp_persistent.spec : Prop := ∀ γ Fh, Persistent (beHookFp (GF := GF) γ Fh)

def beSynced_persistent.spec : Prop := ∀ γ, Persistent (beSynced (GF := GF) γ)

def beDurInv_persistent.spec : Prop := ∀ γ p, Persistent (beDurInv (GF := GF) γ p)

def safeRegOk_persistent.spec : Prop := Persistent (safeRegOk (GF := GF))

def envOk_persistent.spec : Prop := Persistent (envOk (GF := GF))

/-- **`envOk`'s introduction**, from the program-start fact (W0's adequacy lists it). -/
def envOk_intro.spec : Prop := etcdVerifyUnset → ⊢ envOk (GF := GF)

/-- A database file fits the address space bbolt maps (`maxMapSize`, 2^48 on 64-bit Linux). -/
def imgBytes_size.spec : Prop := ∀ (I : Image) (bs : List w8), imgBytes I bs → bs.length < 2 ^ 48

/-- A commit asking nothing. -/
def beReq_true.spec : Prop := ∀ γ (Pk : IProp GF), ⊢ beReq γ Pk iprop(True) iprop(True)

def beReq_persistent.spec : Prop := ∀ γ (Pk X Y : IProp GF), Persistent (beReq γ Pk X Y)

end laws

end Backend
end EtcdGrove
end Perennial
