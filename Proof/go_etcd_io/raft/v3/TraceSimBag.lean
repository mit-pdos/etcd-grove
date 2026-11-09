/-
Lean-first (no Rocq counterpart). Trace-check's S5 (2026-11-09): the specification's bags by their
counts (`BagRep b l`: `b` has no duplicate message, positive counts, and `l`'s counts), which
`simInv` relates to the shares' and tokens' lists; `Bag.with` and `Bag.without` keep it.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceSim

variable [GooseExts]

/-- A bag represents a list: no duplicate message, positive counts, the list's counts. -/
def BagRep (b : Etcdraft.Bag) (l : List Etcdraft.Msg) : Prop :=
  b.domain.Nodup ∧ (∀ it ∈ b, 0 < it.2) ∧ ∀ m, Etcdraft.Bag.count b m = l.count m

theorem bag_count_with_other (b : Etcdraft.Bag) (m m' : Etcdraft.Msg) (h : m' ≠ m) :
    (b.with m').count m = b.count m := by
  unfold Etcdraft.Bag.with Etcdraft.Bag.add
  split
  · unfold Etcdraft.Bag.count
    rw [List.find?_map]
    have : ((fun it : Etcdraft.Msg × Nat => it.1 == m) ∘
        fun it => if (it.1 == m') = true then (it.1, it.2 + 1) else it) = (fun it => it.1 == m) := by
      funext x; simp only [Function.comp]; split
      · rename_i hx; simp at hx; simp [hx]
      · rfl
    rw [this]
    cases hf : b.find? (fun it => it.1 == m) with
    | none => rfl
    | some it =>
      have hit : it.1 = m := by simpa using List.find?_some (p := fun it : Etcdraft.Msg × Nat => it.1 == m) hf
      simp [hit, Ne.symm h]
  · unfold Etcdraft.Bag.count
    rw [List.find?_append]
    cases b.find? (fun it => it.1 == m) with
    | some _ => rfl
    | none => simp [h]

theorem bagRep_with (b : Etcdraft.Bag) (l : List Etcdraft.Msg) (m : Etcdraft.Msg) (h : BagRep b l) :
    BagRep (b.with m) (l ++ [m]) := by
  obtain ⟨hnd, hpos, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · unfold Etcdraft.Bag.with Etcdraft.Bag.add Etcdraft.Bag.domain at *
    split
    · rw [List.map_map]
      have : (Prod.fst ∘ fun it : Etcdraft.Msg × Nat => if (it.1 == m) = true then (it.1, it.2 + 1) else it) =
          Prod.fst := by funext x; simp only [Function.comp]; split <;> rfl
      rw [this]; exact hnd
    · rename_i hany
      rw [List.map_append, List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro x hx y hy; simp at hy; subst hy
      intro e; subst e
      obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hx
      exact hany (List.any_eq_true.2 ⟨it, hit, by simp⟩)
  · unfold Etcdraft.Bag.with Etcdraft.Bag.add
    split
    · intro it hit
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hit
      split
      · simp
      · exact hpos x hx
    · intro it hit
      rw [List.mem_append] at hit
      rcases hit with hit | hit
      · exact hpos it hit
      · simp at hit; subst hit; simp
  · intro x
    by_cases hx : x = m
    · subst hx; rw [bag_count_with_self (b := b), hc]; simp
    · rw [bag_count_with_other b x m (Ne.symm hx), hc]; simp [List.count_append, Ne.symm hx]

theorem bagRep_foldl_with (P' : List Etcdraft.Msg) :
    ∀ (b : Etcdraft.Bag) (l : List Etcdraft.Msg), BagRep b l → BagRep (P'.foldl Etcdraft.Bag.with b) (l ++ P') := by
  induction P' with
  | nil => intro b l h; simpa using h
  | cons m P' ih =>
    intro b l h
    have := ih _ _ (bagRep_with b l m h)
    simpa using this

theorem bagRep_perm (b : Etcdraft.Bag) (l l' : List Etcdraft.Msg) (h : BagRep b l) (hp : l.Perm l') :
    BagRep b l' := ⟨h.1, h.2.1, fun m => by rw [h.2.2 m, hp.count_eq]⟩

/-- The shares' messages after node `i`'s share gains `P'`: a permutation of them with `P'`. -/
theorem flatMap_update_perm {K V : Type} [DecidableEq K] (C : List K) (f g : K → List V) (i : K)
    (hnd : C.Nodup) (hi : i ∈ C) (P' : List V) (hg : g i = f i ++ P') (ho : ∀ j, j ≠ i → g j = f j) :
    (C.flatMap g).Perm (C.flatMap f ++ P') := by
  induction C with
  | nil => simp at hi
  | cons c C ih =>
    simp only [List.flatMap_cons]
    rw [List.nodup_cons] at hnd
    by_cases hc : c = i
    · subst hc
      have hC : C.flatMap g = C.flatMap f := by
        have : ∀ j ∈ C, g j = f j := fun j hj => ho j (fun e => hnd.1 (e ▸ hj))
        clear ih hnd hi hg
        induction C with
        | nil => rfl
        | cons x C ihC =>
          simp only [List.flatMap_cons]
          rw [this x (by simp), ihC (fun j hj => this j (by simp [hj]))]
      rw [hg, hC, List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    · have hi' : i ∈ C := by simp [Ne.symm hc] at hi; exact hi
      rw [ho c hc, List.append_assoc]
      exact List.Perm.append_left _ (ih hnd.2 hi')

/-- `without`'s step on one entry keeps its message. -/
theorem without_step (m : Etcdraft.Msg) (it : Etcdraft.Msg × Nat) :
    ((if (it.1 == m) = true then (if it.2 > 1 then some (it.1, it.2 - 1) else none) else some it) = none ∧
      it.1 = m) ∨
      ∃ n, (if (it.1 == m) = true then (if it.2 > 1 then some (it.1, it.2 - 1) else none) else some it) =
        some (it.1, n) ∧ (it.1 ≠ m → n = it.2) := by
  by_cases h : (it.1 == m) = true
  · simp only [h, ↓reduceIte]
    by_cases h2 : it.2 > 1
    · right; exact ⟨it.2 - 1, by simp [h2], fun hne => absurd (by simpa using h) hne⟩
    · left; exact ⟨by simp [h2], by simpa using h⟩
  · right; refine ⟨it.2, by simp [h], fun _ => rfl⟩

theorem bag_count_without_other (b : Etcdraft.Bag) (m m' : Etcdraft.Msg) (h : m' ≠ m) :
    (b.without m').count m = b.count m := by
  unfold Etcdraft.Bag.without Etcdraft.Bag.sub
  induction b with
  | nil => rfl
  | cons it b ih =>
    rw [List.filterMap_cons]
    rcases without_step m' it with ⟨hn, hit⟩ | ⟨n, hs, hn⟩
    · rw [hn]; simp only; rw [ih, bag_count_cons, hit]; simp [h]
    · rw [hs, bag_count_cons, bag_count_cons, ih]
      by_cases hm : it.1 = m
      · have : it.1 ≠ m' := fun e => h (e ▸ hm)
        simp [hm, hn this]
      · simp [hm]

theorem bag_without_domain (b : Etcdraft.Bag) (m : Etcdraft.Msg) :
    (b.without m).domain.Sublist b.domain := by
  unfold Etcdraft.Bag.without Etcdraft.Bag.sub Etcdraft.Bag.domain
  induction b with
  | nil => simp
  | cons it b ih =>
    rw [List.filterMap_cons]
    rcases without_step m it with ⟨hn, -⟩ | ⟨n, hs, -⟩
    · rw [hn]; exact ih.cons _
    · rw [hs]; simp only [List.map_cons]; exact ih.cons_cons _

theorem bagRep_without (b : Etcdraft.Bag) (l : List Etcdraft.Msg) (m : Etcdraft.Msg) (h : BagRep b l)
    (hm : m ∈ l) : BagRep (b.without m) (l.erase m) := by
  obtain ⟨hnd, hpos, hc⟩ := h
  have hcm : 0 < Etcdraft.Bag.count b m := by rw [hc]; exact List.count_pos_iff.2 hm
  refine ⟨hnd.sublist (bag_without_domain b m), ?_, ?_⟩
  · unfold Etcdraft.Bag.without Etcdraft.Bag.sub
    intro it hit
    obtain ⟨y, hy, hye⟩ := List.mem_filterMap.1 hit
    have hpy := hpos y hy
    by_cases h1 : (y.1 == m) = true
    · by_cases h2 : y.2 > 1
      · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hye; subst hye; simp; omega
      · simp [h1, h2] at hye
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hye; subst hye; exact hpy
  · intro y
    by_cases hy : y = m
    · subst hy
      have := bag_count_without b y hnd hcm
      rw [hc] at this
      rw [List.count_erase_self]; omega
    · rw [bag_count_without_other b y m (Ne.symm hy), hc, List.count_erase_of_ne hy]

end TraceSim

end EtcdGrove
end Perennial
