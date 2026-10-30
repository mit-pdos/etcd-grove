/-
Lean-first (no Rocq counterpart).

# Pure lemmas of the cluster's bring-up (2026-10-30, kvreconf-final, helper LIFE)

The bootstrap voters `bootVoters k` (`1 … k`: distinct, none `0`, exactly the ids in that range),
the size of a replica map whose keys are `1 … nid-1` (`startNew`'s `len(c.replicas)`), and the
fresh ids' list (`freshIds`) losing its head when a replica starts.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

theorem bootVoters_length (k : Nat) : (bootVoters k).length = k := by
  simp [bootVoters]

theorem bootVoters_mem (k : Nat) (hk : k ≤ 10) (i : w64) :
    i ∈ bootVoters k ↔ 1 ≤ uint.nat i ∧ uint.nat i ≤ k := by
  simp only [bootVoters, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; constructor <;> word
  · rintro ⟨h1, h2⟩
    refine ⟨uint.nat i - 1, by omega, ?_⟩
    word

theorem bootVoters_nodup (k : Nat) (hk : k ≤ 10) : (bootVoters k).Nodup := by
  unfold bootVoters
  rw [List.Nodup, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := k))
  intro a b ha hb hne h
  simp only [List.mem_range] at ha hb
  have := congrArg (fun x : w64 => uint.nat x) h
  apply hne
  word

theorem bootVoters_zero (k : Nat) (hk : k ≤ 10) : W64 0 ∉ bootVoters k := by
  rw [bootVoters_mem k hk]; intro h; have := h.1; word

theorem bootVoters_getElem (k : Nat) (j : Nat) (hj : j < k) :
    (bootVoters k)[j]? = some (W64 ((j : Int) + 1)) := by
  simp [bootVoters, hj]

/-- A map whose keys are exactly `1 … nid-1` has `nid - 1` entries. -/
theorem size_of_keys {V : Type} (R : GMap w64 V) (nid : Nat) (hn : nid ≤ 10) (h1 : 1 ≤ nid)
    (hR : ∀ i, (R !! i).isSome ↔ 1 ≤ uint.nat i ∧ uint.nat i < nid) :
    GMap.size R = nid - 1 := by
  rw [GMap.size_eq_length R (bootVoters (nid - 1)) (bootVoters_nodup _ (by omega)), bootVoters_length]
  intro i
  rw [bootVoters_mem _ (by omega), hR]
  omega

theorem freshIds_cons (k : Nat) (hk : k < 10) :
    freshIds k = W64 (k : Int) :: freshIds (k + 1) := by
  unfold freshIds
  have : ∀ n, n ≤ 10 → k < n →
      ((List.range n).filter (fun i => decide (k ≤ i))).map (fun i : Nat => W64 (i : Int)) =
      W64 (k : Int) :: ((List.range n).filter (fun i => decide (k + 1 ≤ i))).map
        (fun i : Nat => W64 (i : Int)) := by
    intro n hn hkn
    induction n with
    | zero => omega
    | succ n IH =>
      rw [List.range_succ, List.filter_append, List.filter_append]
      by_cases hkn' : k < n
      · rw [List.map_append, IH (by omega) hkn', List.map_append]
        simp [show k ≤ n from by omega, show k + 1 ≤ n from by omega]
      · have hkk : k = n := by omega
        subst hkk
        have h0 : (List.range k).filter (fun i => decide (k ≤ i)) = [] := by
          rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp; omega
        have h1 : (List.range k).filter (fun i => decide (k + 1 ≤ i)) = [] := by
          rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp; omega
        simp [h0, h1]
  exact this 10 (by omega) hk

section cs
variable [GooseExts]

theorem life_perm_elements_listToSet (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

theorem life_perm_elements_empty : ([] : List w64) ≡ₚ GMap.elements (∅ : GSet w64) := by
  refine (List.perm_ext_iff_of_nodup List.nodup_nil (GMap.NoDup_elements _)).2 ?_
  intro k
  rw [GMap.elem_of_elements]
  simp only [List.not_mem_nil, false_iff]
  exact GMap.not_elem_of_empty _

/-- The bootstrap conf state reports the voters' simple membership. -/
theorem bootCS_is (vs : List w64) (h : vs.Nodup) :
    confStateIs (bootCS vs) (Membership.simple (GMap.listToSet vs)) :=
  ⟨life_perm_elements_listToSet _ h, life_perm_elements_empty, life_perm_elements_empty,
    life_perm_elements_empty, rfl⟩

end cs

end kvreconf
end EtcdGrove
end Perennial
