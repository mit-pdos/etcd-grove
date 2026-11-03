/-
**The pure vocabulary of a cut image** (F2, stage 2, 2026-11-03): what the batch lock's compaction
tracking (`cmpTrack`, `InvStore.lean`) is written in, moved below `InvStore` from the modules that
defined it (unchanged): the bucket's entries (`KvEnt`, `entsOfRev`, `logEnts`, from
`InvWatchSync.lean`), their bucket (`bucketOfEnts`, from `RestoreCut.lean`), the job's shape
(`entsCutAt`, from `InvIndexRestore.lean`), and the compaction records (`CmpRecs`, `recsOk`,
`recsPos`, from `CmpRecs.lean`; `recBytes`, from `RestoreVocab.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevOrder

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open go_etcd_io.etcd.server.v3.storage.mvcc

/-- The `Key` bucket's written-back contents: a revision's bytes to the encoded key-value. -/
abbrev Bucket := GMap GoString GoString

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

/-- The bytes stored at a record (`RevToBytes(Revision{Main: x})`). -/
def recBytes (x : Option w64) : Option GoString := x.map (fun x => revBytes ⟨x, W64 0⟩ false)

section pure
variable [GooseExts]

/-- The `Key` bucket of the entries `ents` (`bucketMap`'s fold over them). -/
def bucketOfEnts (ents : List KvEnt) : Bucket :=
  (ents.map KvEnt.pair).foldl (fun m p => GMap.insert p.1 p.2 m) GMap.empty

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
end EtcdGrove
end Perennial
