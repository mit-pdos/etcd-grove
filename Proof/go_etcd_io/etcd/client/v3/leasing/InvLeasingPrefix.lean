/-
The leasing KV's reserved prefix (etcd#22118): `deleteIntersectsLeasingPrefix`'s test in the model
(`leaseDelIntersects`), the deletes `validateDelete` rejects (`leaseDelRejected`), and what a
delete the test lets through cannot touch: no key with the prefix, i.e. no lease key, is in its
range (`LeaseKeysOutside`, `leaseDelIntersects_false`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas
public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **`lkv.deleteIntersectsLeasingPrefix(op)`** (`kv.go`) for the prefix `pfx` and the operation
`o`: `o`'s key is in the prefix's range `[pfx, prefixRangeEnd pfx)`, or, for a range (`o`'s end
not empty), the prefix is in `o`'s range; both with the cache's `inRange` (`leaseInRange`, for
which an end `"\x00"` is open-ended). -/
def leaseDelIntersects (pfx : GoString) (o : OpFull) : Bool :=
  if o.base.rangeEnd = [] then leaseInRange o.key pfx (prefixRangeEnd pfx)
  else leaseInRange o.key pfx (prefixRangeEnd pfx) || leaseInRange pfx o.key o.base.rangeEnd

/-- **The operations `validateDelete` rejects**: deletes that intersect the prefix. -/
def leaseDelRejected (pfx : GoString) (o : OpFull) : Bool :=
  decide (o.t = W64 3) && leaseDelIntersects pfx o

/-- **No lease key is in `o`'s range**: no key with the prefix `pfx` (where the leasing KV keeps
its lease keys, `pfx ++ k`) is in `o`'s range, in etcd's sense (`inRange`). A delete of `o`
deletes no lease key. -/
def LeaseKeysOutside (pfx : GoString) (o : OpFull) : Prop :=
  ∀ k, pfx <+: k → inRange o.key o.base.rangeEnd k = false

/-! ## Lemmas -/

theorem goStringLt_of_le_of_lt {a b c : GoString} (h1 : ¬ go.GoStringLt b a)
    (h2 : go.GoStringLt b c) : go.GoStringLt a c := by
  by_cases h : go.GoStringLt a b
  · exact goStringLt_trans h h2
  · rw [goStringLt_eq_of_not_lt h h1]; exact h2

theorem goStringLt_of_lt_of_le {a b c : GoString} (h1 : go.GoStringLt a b)
    (h2 : ¬ go.GoStringLt c b) : go.GoStringLt a c := by
  by_cases h : go.GoStringLt b c
  · exact goStringLt_trans h1 h
  · rw [← goStringLt_eq_of_not_lt h h2]; exact h1

/-- The keys with a non-empty prefix are those in its range, with the cache's `inRange`. -/
theorem leaseInRange_prefix (p k : GoString) (hp : p ≠ []) :
    leaseInRange k p (prefixRangeEnd p) = true ↔ p <+: k := by
  rw [← concurrency.inRange_prefix p k hp]
  have hne := concurrency.prefixRangeEnd_ne_nil p
  unfold leaseInRange inRange
  by_cases h0 : prefixRangeEnd p = [W8 0]
  · simp [h0]
  · have h0' : ¬ prefixRangeEnd p = [0#8] := h0
    simp [h0', hne]

/-- **A delete `deleteIntersectsLeasingPrefix` lets through deletes no lease key.** -/
theorem leaseDelIntersects_false (pfx : GoString) (o : OpFull) (hp : pfx ≠ [])
    (h : leaseDelIntersects pfx o = false) : LeaseKeysOutside pfx o := by
  intro k hk
  have hkey : ¬ pfx <+: o.key := by
    intro hpk
    have := (leaseInRange_prefix pfx o.key hp).2 hpk
    unfold leaseDelIntersects at h
    split at h <;> simp_all
  have hk' := (leaseInRange_prefix pfx k hp).2 hk
  by_cases he : o.base.rangeEnd = []
  · simp only [inRange, he, ite_true, decide_eq_false_iff_not]
    rintro rfl; exact hkey hk
  · have h2 : leaseInRange pfx o.key o.base.rangeEnd = false := by
      unfold leaseDelIntersects at h; simp only [he, ite_false, Bool.or_eq_false_iff] at h
      exact h.2
    cases hin : inRange o.key o.base.rangeEnd k
    · rfl
    exfalso
    -- `k` in `o`'s range: `o.key ≤ k`, and `k < end` unless `end` is `"\x00"`.
    have hkk : ¬ go.GoStringLt k o.key := by
      unfold inRange at hin; split at hin
      · contradiction
      · split at hin <;> simp_all
    unfold leaseInRange at h2 hk'
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true,
      decide_eq_true_eq] at hk'
    by_cases hlt : go.GoStringLt pfx o.key
    · -- `pfx < o.key ≤ k < prefixRangeEnd pfx`: `o.key` has the prefix.
      apply hkey
      apply (leaseInRange_prefix pfx o.key hp).1
      unfold leaseInRange
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true,
        decide_eq_true_eq]
      refine ⟨fun h' => goStringLt_irrefl _ (goStringLt_trans h' hlt), ?_⟩
      rcases hk'.2 with h0 | hpe
      · exact Or.inl h0
      · exact Or.inr (goStringLt_of_le_of_lt hkk hpe)
    · -- `o.key ≤ pfx` and `pfx` not in `o`'s range: `end ≤ pfx ≤ k < end`.
      simp only [hlt, decide_false, Bool.not_false, Bool.true_and, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at h2
      have hke : go.GoStringLt k o.base.rangeEnd := by
        unfold inRange at hin
        simp only [he, ite_false, h2.1, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not, decide_eq_true_eq] at hin
        exact hin.2
      exact hk'.1 (goStringLt_of_lt_of_le hke h2.2)

/-- The converse, read as the PR's policy: a delete whose range has a lease key is rejected. -/
theorem leaseDelIntersects_of_not_outside (pfx : GoString) (o : OpFull) (hp : pfx ≠ [])
    (h : ¬ LeaseKeysOutside pfx o) : leaseDelIntersects pfx o = true := by
  cases hb : leaseDelIntersects pfx o
  · exact absurd (leaseDelIntersects_false pfx o hp hb) h
  · rfl

/-! ## What `delete` and `Commit` guarantee -/

section guard
variable [ext : FfiSyntax]

/-- **The guard of a delete or a transaction** with the plain operations `os`, returning the error
`err`: if one of `os` is a delete intersecting the lease prefix, `err` is an error (etcd#22118's
policy); and on success, no delete of `os` has a lease key in its range. -/
def LeaseDeleteGuard (pfx : GoString) (os : List OpFull) (err : GoInterface) : Prop :=
  ((∃ o ∈ os, leaseDelRejected pfx o = true) → err ≠ GoInterface.nil) ∧
  (err = GoInterface.nil → ∀ o ∈ os, o.t = W64 3 → LeaseKeysOutside pfx o)

/-- The policy implies the guarantee. -/
theorem LeaseDeleteGuard.of_rejects {pfx : GoString} {os : List OpFull} {err : GoInterface}
    (hp : pfx ≠ []) (h : (∃ o ∈ os, leaseDelRejected pfx o = true) → err ≠ GoInterface.nil) :
    LeaseDeleteGuard pfx os err := by
  refine ⟨h, fun he o ho ht => ?_⟩
  by_cases hout : LeaseKeysOutside pfx o
  · exact hout
  · exfalso
    have hi := leaseDelIntersects_of_not_outside pfx o hp hout
    exact h ⟨o, ho, by simp [leaseDelRejected, ht, hi]⟩ he

/-- An error satisfies the guard. -/
theorem LeaseDeleteGuard.of_ne_nil {pfx : GoString} {os : List OpFull} {err : GoInterface}
    (h : err ≠ GoInterface.nil) : LeaseDeleteGuard pfx os err :=
  ⟨fun _ => h, fun he => absurd he h⟩

/-- Success with no rejected delete among `os`. -/
theorem LeaseDeleteGuard.of_none {pfx : GoString} {os : List OpFull} {err : GoInterface}
    (hp : pfx ≠ []) (h : ∀ o ∈ os, leaseDelRejected pfx o = false) :
    LeaseDeleteGuard pfx os err :=
  LeaseDeleteGuard.of_rejects hp (fun ⟨o, ho, hr⟩ => by simp [h o ho] at hr)

end guard

end EtcdGrove
end Perennial
