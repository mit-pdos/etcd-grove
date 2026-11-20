/-
**`SetNodeMap.RecursiveDifference`'s steps** over node lists: the merge invariant `fpC.OInv`
(`LawProofsTrie.lean`) with the paths of the first list none of whose non-empty prefixes is in the
set `B` (`RR`): below a key `k`, nothing when `[k] ∈ B`; else the key's whole column when `B` has no
child `k`, the recursive difference of the two columns when it has one.

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsMerge
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

theorem nePrefixes_cons (k : PE) (r : Path) :
    Path.nePrefixes (k :: r) = [k] :: (Path.nePrefixes r).map (k :: ·) := by
  simp only [Path.nePrefixes, List.length_cons, List.range_succ_eq_map, List.map_cons,
    List.map_map]
  rfl

theorem mem_nePrefixes_cons (k : PE) (r s : Path) :
    s ∈ Path.nePrefixes (k :: r) ↔ s = [k] ∨ ∃ t ∈ Path.nePrefixes r, s = k :: t := by
  rw [nePrefixes_cons, List.mem_cons, List.mem_map]
  constructor
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩

theorem nePrefixes_ne {r t : Path} (h : t ∈ Path.nePrefixes r) : t ≠ [] := by
  simp only [Path.nePrefixes, List.mem_map, List.mem_range] at h
  obtain ⟨n, hn, rfl⟩ := h
  intro he
  rw [List.take_eq_nil_iff] at he
  rcases he with he | rfl
  · omega
  · simp at hn

/-- The paths of `l1` none of whose non-empty prefixes is in `B`. -/
abbrev RR (l1 : NL) (B : PathSet) : Path → Prop :=
  fun q => q ∈ nlPaths l1 ∧ ∀ r ∈ q.nePrefixes, r ∉ B

variable {l1 l2 : NL} {B : PathSet} {i j : Nat} {lo : NL}

/-- `RR`'s column at a key of `l1`. -/
theorem rr_col (h1 : NLok l1) (hB : ∀ q, q ∈ B.deep ↔ q ∈ nlPaths l2) {k : PE} {S : PathSet}
    (hm : (k, S) ∈ l1) (r : Path) :
    RR l1 B (k :: r) ↔ r ∈ S ∧ [k] ∉ B ∧ ∀ t ∈ Path.nePrefixes r, k :: t ∉ nlPaths l2 := by
  simp only [RR]
  rw [nl_col h1 hm r]
  have hdeep : ∀ t ∈ Path.nePrefixes r, (k :: t ∈ B ↔ k :: t ∈ nlPaths l2) := fun t ht => by
    rw [← hB, mem_deep]
    have := nePrefixes_ne ht
    cases t with
    | nil => exact absurd rfl this
    | cons _ _ => simp
  constructor
  · rintro ⟨hr, hp⟩
    refine ⟨hr, hp _ ((mem_nePrefixes_cons k r _).2 (Or.inl rfl)), fun t ht h => ?_⟩
    exact hp _ ((mem_nePrefixes_cons k r _).2 (Or.inr ⟨t, ht, rfl⟩)) ((hdeep t ht).2 h)
  · rintro ⟨hr, hk, ht⟩
    refine ⟨hr, fun s hs => ?_⟩
    rcases (mem_nePrefixes_cons k r s).1 hs with rfl | ⟨t, htm, rfl⟩
    · exact hk
    · exact fun h => ht t htm ((hdeep t htm).1 h)

/-- Under a member `[k]` of `B`, nothing. -/
theorem rr_col_mem (h1 : NLok l1) (hB : ∀ q, q ∈ B.deep ↔ q ∈ nlPaths l2) {k : PE} {S : PathSet}
    (hm : (k, S) ∈ l1) (hk : [k] ∈ B) (r : Path) : ¬ RR l1 B (k :: r) :=
  fun h => ((rr_col h1 hB hm r).1 h).2.1 hk

/-- No child `k` in `B`: the whole column. -/
theorem rr_col_nokey (h1 : NLok l1) (hB : ∀ q, q ∈ B.deep ↔ q ∈ nlPaths l2) {k : PE} {S : PathSet}
    (hm : (k, S) ∈ l1) (hk : [k] ∉ B) (hn : k ∉ keys l2) (r : Path) : RR l1 B (k :: r) ↔ r ∈ S := by
  rw [rr_col h1 hB hm r]
  exact ⟨fun h => h.1, fun h => ⟨h, hk, fun t _ => nl_nokey hn t⟩⟩

/-- A child `k` of `B` with the paths `S2`: the recursive difference of the columns. -/
theorem rr_col_key (h1 : NLok l1) (h2 : NLok l2) (hB : ∀ q, q ∈ B.deep ↔ q ∈ nlPaths l2)
    {k : PE} {S S2 : PathSet} (hm : (k, S) ∈ l1) (hm2 : (k, S2) ∈ l2) (hk : [k] ∉ B) (r : Path) :
    RR l1 B (k :: r) ↔ r ∈ PathSet.rdiff S S2 := by
  rw [rr_col h1 hB hm r, mem_rdiff]
  constructor
  · rintro ⟨hr, -, ht⟩
    exact ⟨hr, fun t htm h => ht t htm ((nl_col h2 hm2 t).2 h)⟩
  · rintro ⟨hr, ht⟩
    exact ⟨hr, hk, fun t htm h => ht t htm ((nl_col h2 hm2 t).1 h)⟩

theorem rd_step1 (h1 : NLok l1) (h2 : NLok l2) (hB : ∀ q, q ∈ B.deep ↔ q ∈ nlPaths l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RR l1 B))
    (hi : i < l1.length) (hj : j < l2.length) (hlt : PE.lt l1[i].1 l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) j ∧
      ([l1[i].1] ∈ B → OInv l1 l2 (i + 1) j lo (RR l1 B)) ∧
      ([l1[i].1] ∉ B → OInv l1 l2 (i + 1) j (lo ++ [l1[i]]) (RR l1 B)) := by
  obtain ⟨hw, hne, hnil⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  have hr := lt_rest_nl h2 hj hw hlt
  have hn := fresh1 h1 hf hi hr
  refine ⟨front_step_x (nlok_sorted h1) hf (by simp [hi]) (by simpa [keys] using hr),
    fun hk => oinv_skip ho (proc_succ1 hi) (rr_col_mem h1 hB (nl_mem_get hi) hk), fun hk => ?_⟩
  have := oinv_add (k := l1[i].1) (S := l1[i].2) ho (proc_succ1 hi) (proc_lt1 hf hi) hw hne hnil
    (rr_col_nokey h1 hB (nl_mem_get hi) hk hn)
  simpa using this

theorem rd_step2 (h1 : NLok l1) (h2 : NLok l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RR l1 B))
    (hi : i < l1.length) (hj : j < l2.length) (hlt : PE.lt l2[j].1 l1[i].1) :
    Front (keys l1) (keys l2) i (j + 1) ∧ OInv l1 l2 i (j + 1) lo (RR l1 B) := by
  obtain ⟨hw, -, -⟩ := h2.2 l2[j].1 l2[j].2 (nl_mem_get hj)
  have hr := lt_rest_nl h1 hi hw hlt
  exact ⟨front_step_y (nlok_sorted h2) hf (by simp [hj]) (by simpa [keys] using hr),
    oinv_skip ho (proc_succ2 hj) (fun r h => nl_nokey (fresh2 h2 hf hj hr) r h.1)⟩

theorem rd_step12 (h1 : NLok l1) (h2 : NLok l2) (hB : ∀ q, q ∈ B.deep ↔ q ∈ nlPaths l2)
    (hf : Front (keys l1) (keys l2) i j) (ho : OInv l1 l2 i j lo (RR l1 B))
    (hi : i < l1.length) (hj : j < l2.length) (he : l1[i].1 = l2[j].1) :
    Front (keys l1) (keys l2) (i + 1) (j + 1) ∧
      ([l1[i].1] ∈ B → OInv l1 l2 (i + 1) (j + 1) lo (RR l1 B)) ∧
      ([l1[i].1] ∉ B → (∃ r, r ∈ PathSet.rdiff l1[i].2 l2[j].2) →
        OInv l1 l2 (i + 1) (j + 1) (lo ++ [(l1[i].1, PathSet.rdiff l1[i].2 l2[j].2)]) (RR l1 B)) ∧
      ([l1[i].1] ∉ B → (∀ r, r ∉ PathSet.rdiff l1[i].2 l2[j].2) →
        OInv l1 l2 (i + 1) (j + 1) lo (RR l1 B)) := by
  obtain ⟨hw, -, hnil⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  have hm2 : (l1[i].1, l2[j].2) ∈ l2 := by rw [he]; exact nl_mem_get hj
  refine ⟨front12 h1 h2 hf hi hj he,
    fun hk => oinv_skip ho (proc_succ12 hi hj he) (rr_col_mem h1 hB (nl_mem_get hi) hk),
    fun hk hne => ?_, fun hk hemp => ?_⟩
  · exact oinv_add ho (proc_succ12 hi hj he) (proc_lt1 hf hi) hw hne
      (fun h => hnil ((mem_rdiff _ _ _).1 h).1) (rr_col_key h1 h2 hB (nl_mem_get hi) hm2 hk)
  · exact oinv_skip ho (proc_succ12 hi hj he)
      (fun r h => hemp r ((rr_col_key h1 h2 hB (nl_mem_get hi) hm2 hk r).1 h))

/-- The rest of `l1` once `B`'s children are consumed, one node at a time. -/
theorem rd_tail (h1 : NLok l1) (hB : ∀ q, q ∈ B.deep ↔ q ∈ nlPaths l2)
    (hf : Front (keys l1) (keys l2) i l2.length) (ho : OInv l1 l2 i l2.length lo (RR l1 B))
    (hi : i < l1.length) :
    Front (keys l1) (keys l2) (i + 1) l2.length ∧
      ([l1[i].1] ∈ B → OInv l1 l2 (i + 1) l2.length lo (RR l1 B)) ∧
      ([l1[i].1] ∉ B → OInv l1 l2 (i + 1) l2.length (lo ++ [l1[i]]) (RR l1 B)) := by
  obtain ⟨hw, hne, hnil⟩ := h1.2 l1[i].1 l1[i].2 (nl_mem_get hi)
  have hn : l1[i].1 ∉ keys l2 := notin_other1 h1 hf (getElem_mem_drop hi)
  refine ⟨front_step_x (nlok_sorted h1) hf (by simp [hi]) (fun b hb => by
      rw [List.drop_of_length_le (by simp [keys])] at hb; simp at hb),
    fun hk => oinv_skip ho (proc_succ1 hi) (rr_col_mem h1 hB (nl_mem_get hi) hk), fun hk => ?_⟩
  have := oinv_add (k := l1[i].1) (S := l1[i].2) ho (proc_succ1 hi) (proc_lt1 hf hi) hw hne hnil
    (rr_col_nokey h1 hB (nl_mem_get hi) hk hn)
  simpa using this

/-- At the end (`l1` consumed): the recursive difference. -/
theorem rd_final (ho : OInv l1 l2 l1.length j lo (RR l1 B))
    (D : PathSet) (hD : ∀ q, q ∈ D ↔ q ∈ nlPaths l1) :
    ∀ q, q ∈ PathSet.rdiff D B ↔ q ∈ nlPaths lo := by
  intro q
  rw [ho.2.2, mem_rdiff, hD]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨⟨h, hn⟩, ?_⟩
    obtain ⟨k, r, rfl, hk⟩ := nl_heads q h; exact ⟨k, r, rfl, proc_all1 hk⟩
  · rintro ⟨⟨h, hn⟩, -⟩
    exact ⟨h, hn⟩

end fpC

end smd
end EtcdGrove
end Perennial
