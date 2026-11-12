/-
**The store's cut: its pure vocabulary** (stage 2, the snapshot image's (a), 2026-11-05; moved here,
unchanged, from `InvStore` (`Bucket`, `keyName`), `InvWatchSync` (`KvEnt`, `entsOfRev`, `logEnts`),
`RestoreCut` (`bucketOfEnts`), `InvIndexRestore` (`entsCutAt`), `CmpRecs` (the records and their
revision), `RestoreVocab` (`recBytes`) and `Api/SnapImage` (`cutOk`, `physLookup`, `jobPast`), so
that the store's invariants (`InvStore`'s `compactRes`) can state the cut of the physical `Key`
bucket that a backend snapshot's observation reads). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-- The `Key` bucket's written-back contents: a revision's bytes to the encoded key-value. -/
abbrev Bucket := GMap GoString GoString

/-- The `Key` bucket's name. -/
abbrev keyName : GoString := go_etcd_io.etcd.server.v3.storage.schema.keyName

/-- A bucket entry as `kvsToEvents` reads it: its revision, whether it is a tombstone, and the
key-value it encodes. -/
structure KvEnt where
  rev : Rev
  tomb : Bool
  kv : EtcdKv

/-- The entry's key and value in the bucket. -/
def KvEnt.pair (e : KvEnt) : GoString × GoString := (revBytes e.rev e.tomb, kvEncode e.kv)

/-- The bucket's entries of revision `r` (changes `cs`, the state `before` before them), in
sub-revision order (`bucketOfRev`'s, as entries). -/
def entsOfRev (r : Nat) (before : List EtcdKv) (cs : List Change) : List KvEnt :=
  cs.zipIdx.filterMap fun p =>
    (changeKv (W64 r) before cs p.2).map fun kv => ⟨⟨W64 r, W64 p.2⟩, p.1.isDel, kv⟩

/-- The bucket's entries of the revisions `[lo, hi)` of `log`, in revision order. -/
def logEnts (log : Log) (lo hi : Nat) : List KvEnt :=
  ((List.range' lo (hi - lo)).map fun m =>
    entsOfRev m (stateAt log (m - 1)) (log.getD m [])).flatten

section pure
variable [GooseExts]

/-- The `Key` bucket of the entries `ents` (`bucketMap`'s fold over them). -/
def bucketOfEnts (ents : List KvEnt) : Bucket :=
  (ents.map KvEnt.pair).foldl (fun m p => GMap.insert p.1 p.2 m) GMap.empty

/-- **The job's shape** (in place of round 3's `bucketThinnedAt`; review round 4, A1 (b)): the image's
`Key` entries `ents` are the log's (in order) but for, per key, a prefix of its entries, each
deletable by the compaction at `c` (`KeyDel`). A finished compaction at `c` (every deletable entry
gone), a leader's bucket mid-job (the job deletes from revision `0` up, in batches, which may stop
between two sub-revisions of one revision), and either after an earlier finished compaction
(`KeyDel` grows with `c`) all have it. -/
def entsCutAt (L : Log) (c : Int) (ents : List KvEnt) : Prop :=
  ents.Sublist (logEnts L 0 L.length) ∧
    (∀ e ∈ logEnts L 0 L.length, e ∉ ents → KeyDel L c (revBytes e.rev e.tomb)) ∧
    ∀ e₁ ∈ logEnts L 0 L.length, ∀ e₂ ∈ logEnts L 0 L.length,
      e₁.kv.key = e₂.kv.key → Rev.lt e₁.rev e₂.rev → e₂ ∉ ents → e₁ ∉ ents

/-- **A backend image's compaction records**: `Meta`'s `finishedCompactRev` and
`scheduledCompactRev`, absent or a revision, what `restore()` reads (`kvstore.go:330-342`). -/
structure CmpRecs where
  fin : Option w64
  sched : Option w64
  deriving DecidableEq

/-- No record (`kbNoCmp`'s backends). -/
def CmpRecs.empty : CmpRecs := ⟨none, none⟩

/-- The finished record, `-1` if absent (`restore()`'s first `compactMainRev`). -/
def CmpRecs.finRev (r : CmpRecs) : Int := (r.fin.map sint.Z).getD (-1)

/-- The scheduled record as `restore()` reads it: `0` if absent (`UnsafeReadScheduledCompact`'s
`(0, false)`, whose found flag `restore()` drops). -/
def CmpRecs.schedRev (r : CmpRecs) : Int := (r.sched.map sint.Z).getD 0

/-- **`restore()` resumes the scheduled compaction**: the scheduled record (read as above) is not
`0` and is past the finished one (`kvstore.go:389-391`, `:411`). A scheduled record of `0` is never
resumed (`nonissues/etcd-restore-scheduled-compact-zero.md`). -/
def CmpRecs.resumes (r : CmpRecs) : Bool := decide (r.schedRev ≠ 0 ∧ r.finRev < r.schedRev)

/-- **The compaction revision `restore()` leaves** (`compactMainRev` after it): the scheduled one if
it is resumed (`compactLockfree` → `updateCompactRev`, which succeeds: past the finished one, and
`currentRev` was raised to it), else the finished one, else `-1`. -/
def CmpRecs.crev (r : CmpRecs) : Int := if r.resumes then r.schedRev else r.finRev

/-- **The records are of the log `L`** (pure): each a revision of `L` (`metaRevVal`'s `0 ≤`; below
`|L|`, so `restore()`'s raise of `currentRev` to the scheduled one leaves `|L| - 1`). -/
def recsOk (L : Log) (r : CmpRecs) : Prop :=
  (∀ x, r.fin = some x → 0 ≤ sint.Z x ∧ sint.Z x < L.length) ∧
  (∀ x, r.sched = some x → 0 ≤ sint.Z x ∧ sint.Z x < L.length)

/-- **The records are past revision `0`** (pure; M2's scope restriction, Q7 (a): every committed
compaction is at a revision `≥ 1`, so the image's records, written by applying them, are;
`nonissues/etcd-restore-scheduled-compact-zero.md`). -/
def recsPos (r : CmpRecs) : Prop :=
  (∀ x, r.fin = some x → 1 ≤ sint.Z x) ∧ (∀ x, r.sched = some x → 1 ≤ sint.Z x)

end pure

end mvcc

/-- The bytes stored at a record (`RevToBytes(Revision{Main: x})`). -/
def mvcc.recBytes (x : Option w64) : Option GoString := x.map (fun x => mvcc.revBytes ⟨x, W64 0⟩ false)


namespace mvcc
namespace snap

section pure
variable [GooseExts]

/-- **The store's cut fact** at its log `L`, its view `m` of the `Key` bucket (the backend's
logical view) and the entries `X` the backend records as deleted (`dlsOwn`'s value): the physical
bucket (`m` but `X`) is the entries `ents` cut at `c`. -/
def cutOk (L : Log) (m : Bucket) (X : backend.VData) (c : Int) : Prop :=
  ∃ ents : List KvEnt, entsCutAt L c ents ∧
    ∀ k, (if (X.lookup (keyName, k)).isSome then none else m.lookup k) = (bucketOfEnts ents).lookup k

/-- The physical `Key` bucket: the logical view `m` but the deleted entries `X`. -/
def physLookup (m : Bucket) (X : backend.VData) (k : GoString) : Option GoString :=
  if (X.lookup (keyName, k)).isSome then none else m.lookup k

/-- **The running job's loop invariant** (`entsCutAt_jobStep`'s `hpast`) at its compaction
revision `c₁` and cursor `p`: every entry below the cursor that compaction at `c₁` deletes is gone
from the physical bucket's entries `ents`. What the store must keep with the cut between the job's
batches (the snapshot image's (a)). -/
def jobPast (L : Log) (c₁ : Int) (p : Rev) (ents : List KvEnt) : Prop :=
  ∀ e' ∈ logEnts L 0 L.length, Rev.lt e'.rev p → KeyDel L c₁ (revBytes e'.rev e'.tomb) → e' ∉ ents

/-- **The store's tracked compaction** (the snapshot image's (a), 2026-11-05: what the batch lock's
resource keeps of a compacting real backend, `compactRes`'s `cmpTrack`) at its log `L`, its logical
view `m` of the `Key` bucket, the entries `X` the backend records deleted, the meta keys' records
`rc` and the last job's revision and cursor `jc`: the physical bucket is entries cut at the records'
compaction revision (`cutOk`'s, with the witness kept for the job's cursor), the records of `L`
past `0`, every recorded delete one compaction at that revision may make, and the last job's loop
invariant (`jobPast`) with its revision between the finished record and the compaction revision
(the jobs run one after the other, `compactTok`). -/
def cmpOk (L : Log) (m : Bucket) (X : backend.VData) (rc : CmpRecs) (jc : Int × Rev) : Prop :=
  ∃ ents : List KvEnt, entsCutAt L rc.crev ents ∧
    (∀ k, physLookup m X k = (bucketOfEnts ents).lookup k) ∧
    recsOk L rc ∧ recsPos rc ∧
    (∀ k, (X.lookup (keyName, k)).isSome → KeyDel L rc.crev k) ∧
    jobPast L jc.1 jc.2 ents ∧ -1 ≤ jc.1 ∧ jc.1 ≤ rc.crev ∧ rc.finRev ≤ jc.1

end pure

end snap
end mvcc
end EtcdGrove
end Perennial
