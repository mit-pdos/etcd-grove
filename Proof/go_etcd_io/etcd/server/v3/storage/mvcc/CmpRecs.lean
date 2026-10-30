/-
**A backend image's compaction records** (M2, the storage side, 2026-10-30: review round 3's F1,
round 4's A1 (a); the approval's items 28 and 29, switched): `CmpRecs` (the two compaction keys'
records, what `restore()` reads) with the revision `restore()` leaves (`crev`), the records of a log
(`recsOk`) and past revision `0` (`recsPos`, M2's scope restriction, item 35), and the reader of the
compaction keys under an optional record set (`metaReadSpecR`, review round 5's S1: `none`,
`metaReadSpec rt false`; `some r`, the records exactly), which
`UnsafeReadFinishedCompact`/`UnsafeReadScheduledCompact` read through. The rest of the records
vocabulary (`kbRecs` and the backend's merged compaction-key ghost, `keyReadLocked`'s records
parameter, `storeBackendTR`, `restoreViewR`) is still `M2StorageDraftRestore.lean`'s.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section pure
variable [GooseExts]


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
resumed (`issues/etcd-restore-scheduled-compact-zero.md`). -/
def CmpRecs.resumes (r : CmpRecs) : Bool := decide (r.schedRev ≠ 0 ∧ r.finRev < r.schedRev)

/-- **The compaction revision `restore()` leaves** (`compactMainRev` after it): the scheduled one if
it is resumed (`compactLockfree` → `updateCompactRev`, which succeeds: past the finished one, and
`currentRev` was raised to it), else the finished one, else `-1`. -/
def CmpRecs.crev (r : CmpRecs) : Int := if r.resumes then r.schedRev else r.finRev

theorem CmpRecs.crev_empty : CmpRecs.empty.crev = -1 := by decide

theorem CmpRecs.resumes_empty : CmpRecs.empty.resumes = false := by decide

/-- **The records are of the log `L`** (pure): each a revision of `L` (`metaRevVal`'s `0 ≤`; below
`|L|`, so `restore()`'s raise of `currentRev` to the scheduled one leaves `|L| - 1`). -/
def recsOk (L : Log) (r : CmpRecs) : Prop :=
  (∀ x, r.fin = some x → 0 ≤ sint.Z x ∧ sint.Z x < L.length) ∧
  (∀ x, r.sched = some x → 0 ≤ sint.Z x ∧ sint.Z x < L.length)

/-- **The records' sign** (M2's restore chain, item 30's D2): each record a revision (`≥ 0`), as
`metaReadSpecR … (some r)` states of what it reads; `recsOk` gives it. -/
def recsSign (r : CmpRecs) : Prop :=
  (∀ x, r.fin = some x → 0 ≤ sint.Z x) ∧ (∀ x, r.sched = some x → 0 ≤ sint.Z x)

theorem recsOk_sign (L : Log) (r : CmpRecs) (h : recsOk L r) : recsSign r :=
  ⟨fun x hx => (h.1 x hx).1, fun x hx => (h.2 x hx).1⟩

/-- The restored revision is a revision of the log (or `-1`). -/
theorem recsOk_crev_lt (L : Log) (r : CmpRecs) (h : recsOk L r) (hL : 2 ≤ L.length) :
    r.crev < L.length := by
  have hf : ∀ x, r.fin = some x → sint.Z x < L.length := fun x hx => (h.1 x hx).2
  have hs : ∀ x, r.sched = some x → sint.Z x < L.length := fun x hx => (h.2 x hx).2
  unfold CmpRecs.crev CmpRecs.schedRev CmpRecs.finRev
  rcases r with ⟨_ | x, _ | y⟩ <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] at hf hs ⊢
  · split <;> omega
  · have := hs y rfl; split <;> omega
  · have := hf x rfl; split <;> omega
  · have := hf x rfl; have := hs y rfl; split <;> omega

/-- **The records are past revision `0`** (pure; M2's scope restriction, Q7 (a): every committed
compaction is at a revision `≥ 1`, so the image's records, written by applying them, are;
`issues/etcd-restore-scheduled-compact-zero.md`). -/
def recsPos (r : CmpRecs) : Prop :=
  (∀ x, r.fin = some x → 1 ≤ sint.Z x) ∧ (∀ x, r.sched = some x → 1 ≤ sint.Z x)

/-- **Under the scope restriction the restored revision is none or a compaction's** (`-1` or
`≥ 1`): the corner of Q7 (a scheduled compaction at `0`, never resumed) cannot arise. -/
theorem recsPos_crev (r : CmpRecs) (h : recsPos r) : r.crev = -1 ∨ 1 ≤ r.crev := by
  have hf : ∀ x, r.fin = some x → 1 ≤ sint.Z x := h.1
  have hs : ∀ x, r.sched = some x → 1 ≤ sint.Z x := h.2
  unfold CmpRecs.crev CmpRecs.resumes CmpRecs.schedRev CmpRecs.finRev
  rcases r with ⟨_ | x, _ | y⟩ <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] at hf hs ⊢
  · left; simp
  · have := hs y rfl
    have h0 : sint.Z y ≠ 0 := by omega
    have h1 : (-1 : Int) < sint.Z y := by omega
    right; simp [h0, h1]; omega
  · have := hf x rfl
    right; simp; omega
  · have := hf x rfl; have := hs y rfl
    have h0 : sint.Z y ≠ 0 := by omega
    right
    by_cases hc : sint.Z x < sint.Z y <;> simp [h0, hc] <;> omega

/-- The record a compaction key holds. -/
def CmpRecs.at (r : CmpRecs) (kn : GoString) : Option w64 :=
  if kn = finKeyBytes then r.fin else r.sched

theorem CmpRecs.at_fin (r : CmpRecs) : r.at finKeyBytes = r.fin := by
  unfold CmpRecs.at; simp

theorem CmpRecs.at_sched (r : CmpRecs) : r.at schedKeyBytes = r.sched := by
  unfold CmpRecs.at; simp [finKeyBytes, schedKeyBytes]

/-- The records' sign, key by key. -/
theorem recsSign_at (r : CmpRecs) (h : recsSign r) (kn : GoString) (x : w64)
    (hx : r.at kn = some x) : 0 ≤ sint.Z x := by
  unfold CmpRecs.at at hx
  split at hx
  · exact h.1 x hx
  · exact h.2 x hx

end pure

section reader
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A read of a compaction key under the records `rs`** (review round 5's S1: one reader
predicate with an optional record set): `none`, a value the store wrote (`metaReadSpec rt false`:
`checkPrevCompactionCompleted`'s reader); `some r`, exactly the records `r`: at no record, nothing
(`metaReadSpec rt true`, `kbNoCmp`'s reader), else the key's record: nothing if absent, else the
key and the record's bytes, a non-negative revision. `keyReadLocked`'s meta clause gives it at the
records `NC` stands for; `UnsafeReadFinishedCompact`/`UnsafeReadScheduledCompact` return them. -/
def metaReadSpecR (rt : GoInterfaceOk) (rs : Option CmpRecs) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) : IProp GF :=
  match rs with
  | none => metaReadSpec rt false Rd Tok
  | some r =>
    if r = CmpRecs.empty then metaReadSpec rt true Rd Tok
    else iprop(∀ (b : GoInterface) (key : GoSlice) (kn : GoString) (dq : DFrac),
      ⌜metaCompactKey kn⌝ →
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ∗ Tok ∗ key ↦*{dq} kn }}
        (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
          (Val #(slice.nil))) (Val #(W64 0)))
      {{ (ks vs : GoSlice), RET (PairV #ks #vs); Tok ∗ key ↦*{dq} kn ∗
          ((⌜r.at kn = none⌝ ∗ ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice)) ∨
            ∃ (ksl vsl : GoSlice) (x : w64), ⌜r.at kn = some x ∧ 0 ≤ sint.Z x⌝ ∗ ks ↦*□ [ksl] ∗
              Rd ksl kn ∗ vs ↦*□ [vsl] ∗ Rd vsl (revBytes ⟨x, W64 0⟩ false)) }})

instance metaReadSpecR_persistent (rt : GoInterfaceOk) (rs : Option CmpRecs)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    Persistent (metaReadSpecR (GF := GF) rt rs Rd Tok) := by
  unfold metaReadSpecR; split
  · infer_instance
  · split <;> infer_instance

/-- At no record, `kbNoCmp`'s reader. -/
theorem metaReadSpecR_empty (rt : GoInterfaceOk) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) :
    metaReadSpecR (GF := GF) rt (some CmpRecs.empty) Rd Tok = metaReadSpec rt true Rd Tok := by
  unfold metaReadSpecR; simp

/-- At `none`, a value the store wrote. -/
theorem metaReadSpecR_none (rt : GoInterfaceOk) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) :
    metaReadSpecR (GF := GF) rt none Rd Tok = metaReadSpec rt false Rd Tok := rfl

end reader

end mvcc
end EtcdGrove
end Perennial
