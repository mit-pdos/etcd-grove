/-
Pure lemmas of `hashMap.mergeSpans` (its segments of consecutive ids), ported from the old proof's
`hashMap__mergeSpans.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashLemmas
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.ArrayLemmas

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

/-- Two sets with the same elements are equal. -/
theorem unit_map_eq {M1 M2 : GMap w64 Unit} (h : ∀ x, (M1 !! x).isSome ↔ (M2 !! x).isSome) :
    M1 = M2 := by
  apply GMap.map_eq; intro k
  have := h k
  cases h1 : M1 !! k <;> cases h2 : M2 !! k <;> simp_all

/-- `n ≥ 1` consecutive ids of `f` from position `st` (the first `a`): they are the ids from
`a` on, the last `a + n - 1`. -/
theorem seg_mem {f : List w64} {st n : Nat} {a : w64} (hlen : st + n ≤ f.length) (hn : 1 ≤ n)
    (ha : f[st]? = some a) (hc : ∀ j, st ≤ j → j + 1 < st + n → consec f j) :
    a.toNat + n ≤ 2 ^ 64 ∧ (∀ x, x ∈ (f.drop st).take n ↔ inRun a n x) ∧
    ∀ b, f[st + n - 1]? = some b → b.toNat = a.toNat + (n - 1) := by
  have hv : ∀ k, st ≤ k → k < st + n →
      f[k]? = some (f.getD k 0) ∧ (f.getD k 0).toNat = a.toNat + (k - st) := by
    intro k h1 h2
    refine ⟨by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp, ?_⟩
    have := consec_sum (f := f) (st := st) (k - st) (fun j h1' h2' => hc j h1' (by omega))
    rw [show st + (k - st) = k by omega, getD_of_some ha] at this; word
  have hlast := (hv (st + n - 1) (by omega) (by omega)).2
  have hb64 : (f.getD (st + n - 1) 0).toNat < 2 ^ 64 := by word
  refine ⟨by omega, fun x => ?_, fun b hb => ?_⟩
  · rw [List.mem_iff_getElem?]
    constructor
    · rintro ⟨k, hk⟩
      rw [List.getElem?_take] at hk
      split at hk
      · rename_i hkn
        rw [List.getElem?_drop] at hk
        obtain ⟨e1, e2⟩ := hv (st + k) (by omega) (by omega)
        rw [e1] at hk; cases hk
        unfold inRun; rw [e2]; omega
      · cases hk
    · intro hx
      unfold inRun at hx
      refine ⟨(x.toNat - a.toNat), ?_⟩
      rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]
      obtain ⟨e1, e2⟩ := hv (st + (x.toNat - a.toNat)) (by omega) (by omega)
      rw [e1]
      congr 1
      have : (f.getD (st + (x.toNat - a.toNat)) 0).toNat = x.toNat := by rw [e2]; omega
      word
  · obtain ⟨e1, e2⟩ := hv (st + n - 1) (by omega) (by omega)
    rw [e1] at hb; cases hb; rw [e2]; omega

/-- One merged segment of the sorted ids, from position `st` to `i - 1` (ids `a` to `b`): the
preconditions of `mergeWithExistingSpan(a, b)` on the free ids `fk` (the free ids and the
segments before), and the free ids after it. -/
theorem seg_step {ys' free fk : List w64} {st i : Nat} {a b : w64}
    (hfnd : (free ++ ys').Nodup) (hge : ∀ x ∈ free ++ ys', 2 ≤ x.toNat) (hst : st < i)
    (hi : i ≤ ys'.length) (ha : ys'[st]? = some a) (hb : ys'[i - 1]? = some b)
    (hc : ∀ j, st ≤ j → j + 1 < i → consec ys' j) (hfk : fk.Perm (free ++ ys'.take st))
    (hlen : free.length + ys'.length < 2 ^ 63) :
    a.toNat ≤ b.toNat ∧ 1 ≤ a.toNat ∧ (∀ x ∈ fk, 1 ≤ x.toNat) ∧
    (∀ x, inRun a ((b - a).toNat + 1) x → x ∉ fk) ∧
    fk.length + ((b - a).toNat + 1) < 2 ^ 63 ∧
    ∀ fk' : List w64, fk'.Perm (fk ++ runIds a ((b - a).toNat + 1)) → fk'.Perm (free ++ ys'.take i) := by
  have hnd' : ys'.Nodup := (List.nodup_append.1 hfnd).2.1
  obtain ⟨hnw, hmem, hbv⟩ := seg_mem (f := ys') (st := st) (n := i - st) (by omega) (by omega) ha
    (fun j h1 h2 => hc j h1 (by omega))
  have hbz := hbv b (by rw [show st + (i - st) - 1 = i - 1 by omega]; exact hb)
  have hn : (b - a).toNat + 1 = i - st := by word
  rw [hn]
  have hsegsub : ∀ x, x ∈ (ys'.drop st).take (i - st) → x ∈ ys'.drop st :=
    fun x hx => List.take_subset _ _ hx
  have hdd := List.nodup_append.1 (by rw [List.take_append_drop]; exact hnd' :
    (ys'.take st ++ ys'.drop st).Nodup)
  have hfl : fk.length = free.length + st := by
    rw [hfk.length_eq, List.length_append, List.length_take]; omega
  refine ⟨by omega, by have := hge a (List.mem_append_right _ (List.mem_of_getElem? ha)); omega, fun x hx => ?_,
    fun x hx hxf => ?_, by omega, fun fk' hfk' => ?_⟩
  · have := hge x (by
      rcases List.mem_append.1 (hfk.mem_iff.1 hx) with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.take_subset _ _ h))
    omega
  · have hxs := hsegsub x ((hmem x).2 hx)
    rcases List.mem_append.1 (hfk.mem_iff.1 hxf) with h | h
    · exact (List.nodup_append.1 hfnd).2.2 x h x (List.drop_subset _ _ hxs) rfl
    · exact hdd.2.2 x h x hxs rfl
  · have hseg : (runIds a (i - st)).Perm ((ys'.drop st).take (i - st)) :=
      perm_of_mem (runIds_nodup hnw) ((hdd.2.1.sublist (List.take_sublist _ _)))
        (fun x => by rw [mem_runIds hnw, hmem x])
    refine hfk'.trans ((List.Perm.append hfk hseg).trans ?_)
    rw [List.append_assoc, ← List.take_add, show st + (i - st) = i by omega]


end bbolt
end EtcdGrove
end Perennial
