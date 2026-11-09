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

end TraceSim

end EtcdGrove
end Perennial
