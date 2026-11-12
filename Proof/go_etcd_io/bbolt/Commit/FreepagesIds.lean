/-
The ids `DB.freepages` returns (`freeIdsOf C`, U10d of `notes/bbolt-proof-plan.md`): membership,
increasing, at least 2, fewer than `2 ^ 63` under `C.hwm ≤ 2 ^ 62`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section ids
variable [GooseExts]

omit [GooseExts] in
private theorem toNat_W64_nat (x : Nat) (h : x < 2 ^ 64) : (W64 (x : Int)).toNat = x := by
  simp [W64]; omega

/-- The ids of `[2, hwm)` no tree page covers. -/
theorem mem_freeIdsOf (C : CommitSt) (hh : C.hwm ≤ 2 ^ 64) (x : w64) :
    x ∈ freeIdsOf C ↔ 2 ≤ x.toNat ∧ x.toNat < C.hwm ∧ ¬ coversSlot C.pages x.toNat := by
  unfold freeIdsOf
  simp only [List.mem_map, List.mem_filter, List.mem_range', decide_eq_true_eq]
  constructor
  · rintro ⟨n, ⟨⟨i, hi, rfl⟩, hc⟩, rfl⟩
    rw [toNat_W64_nat _ (by omega)]
    exact ⟨by omega, by omega, hc⟩
  · rintro ⟨h2, hlt, hc⟩
    refine ⟨x.toNat, ⟨⟨x.toNat - 2, by omega, by omega⟩, hc⟩, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [toNat_W64_nat _ (by omega)]

theorem freeIdsOf_two (C : CommitSt) (hh : C.hwm ≤ 2 ^ 64) : ∀ x ∈ freeIdsOf C, 2 ≤ x.toNat :=
  fun x hx => ((mem_freeIdsOf C hh x).1 hx).1

theorem freeIdsOf_incr (C : CommitSt) (hh : C.hwm ≤ 2 ^ 64) : PgidsIncr (freeIdsOf C) := by
  unfold PgidsIncr freeIdsOf
  rw [List.pairwise_map]
  refine List.Pairwise.filter _ ?_
  have hp : (List.range' 2 (C.hwm - 2)).Pairwise (· < ·) := List.pairwise_lt_range'
  refine hp.imp_of_mem ?_
  intro a b ha hb hab
  rw [List.mem_range'] at ha hb
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  rw [toNat_W64_nat _ (by omega), toNat_W64_nat _ (by omega)]
  exact hab

theorem freeIdsOf_length (C : CommitSt) : (freeIdsOf C).length ≤ C.hwm - 2 := by
  unfold freeIdsOf
  rw [List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem freeIdsOf_nodup (C : CommitSt) (hh : C.hwm ≤ 2 ^ 64) : (freeIdsOf C).Nodup :=
  (freeIdsOf_incr C hh).imp fun h e => by rw [e] at h; omega

/-- What `DB.freepages`' post states of its ids. -/
theorem freeIdsOf_facts (C : CommitSt) (hh : C.hwm ≤ 2 ^ 62) :
    PgidsIncr (freeIdsOf C) ∧ (∀ x ∈ freeIdsOf C, 2 ≤ x.toNat) ∧ (freeIdsOf C).length < 2 ^ 63 :=
  ⟨freeIdsOf_incr C (by omega), freeIdsOf_two C (by omega),
    by have := freeIdsOf_length C; omega⟩

end ids

end bbolt
end EtcdGrove
end Perennial
