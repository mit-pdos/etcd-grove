/-
**`SetNodeMap.Intersection`'s and `SetNodeMap.Difference`'s steps** over node lists (the merge
invariant `fpC.OInv` of `LawProofsTrie.lean`, with the paths each operation keeps).

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsTrie
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace fpC

/-- A node list's paths have two elements or more. -/
theorem nl_len2 {l : NL} (hl : NLok l) (q : Path) (h : q ∈ nlPaths l) : 2 ≤ q.length := by
  rw [mem_nlPaths] at h
  obtain ⟨k, S, r, hm, hr, rfl⟩ := h
  have hnil := (hl.2 k S hm).2.2
  cases r with
  | nil => exact absurd hr hnil
  | cons _ _ => simp

theorem proc_all1 {l1 l2 : NL} {j : Nat} {k : PE} (hk : k ∈ keys l1) : proc l1 l2 l1.length j k :=
  Or.inl (by rw [List.take_of_length_le (by simp [keys])]; exact hk)

theorem proc_all2 {l1 l2 : NL} {i : Nat} {k : PE} (hk : k ∈ keys l2) : proc l1 l2 i l2.length k :=
  Or.inr (by rw [List.take_of_length_le (by simp [keys])]; exact hk)

/-! ## Intersection -/

/-- The paths both node lists hold. -/
abbrev RI (l1 l2 : NL) : Path → Prop := fun q => q ∈ nlPaths l1 ∧ q ∈ nlPaths l2

variable {l1 l2 : NL} {i j : Nat} {lo : NL}

theorem inter_step1 (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RI l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (hlt : PE.lt l1[i].1 l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) j ∧ OInv l1 l2 (i + 1) j lo (RI l1 l2) := by
  obtain ⟨hw, -, -⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  have hr := lt_rest_nl h2 hj hw hlt
  exact ⟨front_step_x (nlok_sorted h1) hf (by simp [hi]) (by simpa [keys] using hr),
    oinv_skip ho (proc_succ1 hi) (fun r h => nl_nokey (fresh1 h1 hf hi hr) r h.2)⟩

theorem inter_step2 (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RI l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (hlt : PE.lt l2[j].1 l1[i].1) :
    Front (keys l1) (keys l2) i (j + 1) ∧ OInv l1 l2 i (j + 1) lo (RI l1 l2) := by
  obtain ⟨hw, -, -⟩ := h2.2 l2[j].1 l2[j].2 (nl_mem_get hj)
  have hr := lt_rest_nl h1 hi hw hlt
  exact ⟨front_step_y (nlok_sorted h2) hf (by simp [hj]) (by simpa [keys] using hr),
    oinv_skip ho (proc_succ2 hj) (fun r h => nl_nokey (fresh2 h2 hf hj hr) r h.1)⟩

theorem front12 (h1 : NLok l1) (h2 : NLok l2) (hf : Front (keys l1) (keys l2) i j)
    (hi : i < l1.length) (hj : j < l2.length) (he : l1[i].1 = l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) (j + 1) :=
  front_step_eq (nlok_sorted h1) (nlok_sorted h2) hf (by simp [hi]) (by simp [hj])
    (by simpa [keys] using he)

theorem inter_step12 (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RI l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (he : l1[i].1 = l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) (j + 1) ∧
      ((∃ r, r ∈ PathSet.inter l1[i].2 l2[j].2) →
        OInv l1 l2 (i + 1) (j + 1) (lo ++ [(l1[i].1, PathSet.inter l1[i].2 l2[j].2)]) (RI l1 l2)) ∧
      ((∀ r, r ∉ PathSet.inter l1[i].2 l2[j].2) → OInv l1 l2 (i + 1) (j + 1) lo (RI l1 l2)) := by
  obtain ⟨hw, -, hnil⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  have hcol : ∀ r, RI l1 l2 (l1[i].1 :: r) ↔ r ∈ PathSet.inter l1[i].2 l2[j].2 := fun r => by
    simp only [RI]
    rw [mem_pinter, nl_col' h1 (nl_mem_get hi) r]
    have : l1[i].1 = l2[j].1 := he
    rw [this, nl_col' h2 (nl_mem_get hj) r]
  refine ⟨front12 h1 h2 hf hi hj he, fun hne => ?_, fun hemp => ?_⟩
  · exact oinv_add ho (proc_succ12 hi hj he) (proc_lt1 hf hi) hw hne
      (fun h => hnil ((mem_pinter _ _ _).1 h).1) hcol
  · exact oinv_skip ho (proc_succ12 hi hj he) (fun r h => hemp r ((hcol r).1 h))

theorem inter_final (ho : OInv l1 l2 i j lo (RI l1 l2)) (hend : i = l1.length ∨ j = l2.length)
    (D1 D2 : PathSet) (hD1 : ∀ q, q ∈ D1 ↔ q ∈ nlPaths l1) (hD2 : ∀ q, q ∈ D2 ↔ q ∈ nlPaths l2) :
    ∀ q, q ∈ PathSet.inter D1 D2 ↔ q ∈ nlPaths lo := by
  intro q
  rw [ho.2.2, mem_pinter, hD1, hD2]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rcases hend with rfl | rfl
    · obtain ⟨k, r, rfl, hk⟩ := nl_heads q h.1; exact ⟨k, r, rfl, proc_all1 hk⟩
    · obtain ⟨k, r, rfl, hk⟩ := nl_heads q h.2; exact ⟨k, r, rfl, proc_all2 hk⟩
  · exact fun h => h.1

/-! ## Difference -/

/-- The paths of the first node list not in the second. -/
abbrev RD (l1 l2 : NL) : Path → Prop := fun q => q ∈ nlPaths l1 ∧ q ∉ nlPaths l2

theorem diff_step1 (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RD l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (hlt : PE.lt l1[i].1 l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) j ∧ OInv l1 l2 (i + 1) j (lo ++ [l1[i]]) (RD l1 l2) := by
  obtain ⟨hw, hne, hnil⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  have hr := lt_rest_nl h2 hj hw hlt
  refine ⟨front_step_x (nlok_sorted h1) hf (by simp [hi]) (by simpa [keys] using hr), ?_⟩
  have := oinv_add (k := l1[i].1) (S := l1[i].2) ho (proc_succ1 hi) (proc_lt1 hf hi) hw hne hnil
    (fun r => by
      simp only [RD]
      rw [nl_col' h1 (nl_mem_get hi) r]
      have := nl_nokey (fresh1 h1 hf hi hr) r
      exact ⟨fun h => h.1, fun h => ⟨h, this⟩⟩)
  simpa using this

theorem diff_step2 (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RD l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (hlt : PE.lt l2[j].1 l1[i].1) :
    Front (keys l1) (keys l2) i (j + 1) ∧ OInv l1 l2 i (j + 1) lo (RD l1 l2) := by
  obtain ⟨hw, -, -⟩ := h2.2 l2[j].1 l2[j].2 (nl_mem_get hj)
  have hr := lt_rest_nl h1 hi hw hlt
  exact ⟨front_step_y (nlok_sorted h2) hf (by simp [hj]) (by simpa [keys] using hr),
    oinv_skip ho (proc_succ2 hj) (fun r h => nl_nokey (fresh2 h2 hf hj hr) r h.1)⟩

theorem diff_step12 (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RD l1 l2))
    (hi : i < l1.length) (hj : j < l2.length) (he : l1[i].1 = l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) (j + 1) ∧
      ((∃ r, r ∈ PathSet.diff l1[i].2 l2[j].2) →
        OInv l1 l2 (i + 1) (j + 1) (lo ++ [(l1[i].1, PathSet.diff l1[i].2 l2[j].2)]) (RD l1 l2)) ∧
      ((∀ r, r ∉ PathSet.diff l1[i].2 l2[j].2) → OInv l1 l2 (i + 1) (j + 1) lo (RD l1 l2)) := by
  obtain ⟨hw, -, hnil⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  have hcol : ∀ r, RD l1 l2 (l1[i].1 :: r) ↔ r ∈ PathSet.diff l1[i].2 l2[j].2 := fun r => by
    simp only [RD]
    rw [mem_pdiff, nl_col' h1 (nl_mem_get hi) r]
    have : l1[i].1 = l2[j].1 := he
    rw [this, nl_col' h2 (nl_mem_get hj) r]
  refine ⟨front12 h1 h2 hf hi hj he, fun hne => ?_, fun hemp => ?_⟩
  · exact oinv_add ho (proc_succ12 hi hj he) (proc_lt1 hf hi) hw hne
      (fun h => hnil ((mem_pdiff _ _ _).1 h).1) hcol
  · exact oinv_skip ho (proc_succ12 hi hj he) (fun r h => hemp r ((hcol r).1 h))

theorem diff_tail1 (h1 : NLok l1) (hi : i ≤ l1.length)
    (hf : Front (keys l1) (keys l2) i l2.length) (ho : OInv l1 l2 i l2.length lo (RD l1 l2)) :
    OInv l1 l2 l1.length l2.length (lo ++ l1.drop i) (RD l1 l2) :=
  oinv_tail1 h1 _ i lo rfl hi ho hf (fun k S r hm => by
    simp only [RD]
    rw [nl_col h1 (List.mem_of_mem_drop hm) r]
    have := nl_nokey (notin_other1 h1 hf hm) r
    exact ⟨fun h => h.1, fun h => ⟨h, this⟩⟩)

/-- At the end (`l1` consumed): the paths of `D` not in the set `B`, whose deep paths `l2`
holds. -/
theorem diff_final (h1 : NLok l1) (ho : OInv l1 l2 l1.length j lo (RD l1 l2))
    (D B : PathSet) (hD : ∀ q, q ∈ D ↔ q ∈ nlPaths l1) (hB : ∀ q, q ∈ B.deep ↔ q ∈ nlPaths l2) :
    ∀ q, q ∈ PathSet.diff D B ↔ q ∈ nlPaths lo := by
  intro q
  rw [ho.2.2, mem_pdiff, hD]
  have hBq : q ∈ nlPaths l1 → (q ∈ B ↔ q ∈ nlPaths l2) := fun h => by
    rw [← hB, mem_deep]
    exact ⟨fun hb => ⟨hb, nl_len2 h1 q h⟩, fun hb => hb.1⟩
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨⟨h, fun h' => hn ((hBq h).2 h')⟩, ?_⟩
    obtain ⟨k, r, rfl, hk⟩ := nl_heads q h; exact ⟨k, r, rfl, proc_all1 hk⟩
  · rintro ⟨⟨h, hn⟩, -⟩
    exact ⟨h, fun h' => hn ((hBq h).1 h')⟩

end fpC

end smd
end EtcdGrove
end Perennial
