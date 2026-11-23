/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecPure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Pure lemmas for the recovery's Go functions against the model (Spec/swift/Model/Defs.lean):
`recReaches` is complete (with `recReaches_sound`: it decides reachability through the kept
dependencies), so any correct reachability test computes it.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Recover

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- `recReaches`' step. -/
def reachStep (k : Kept) (seen : List CmdId) : List CmdId :=
  (seen ++ (seen.flatMap (kdeps k))).eraseDups

theorem recReaches_eq (k : Kept) (src dst : CmdId) :
    recReaches k src dst = decide (dst ∈ (iter (reachStep k) (k.length + 1) [src]).flatMap (kdeps k)) := rfl

theorem reachStep_mem {k : Kept} {s : List CmdId} {y : CmdId} :
    y ∈ reachStep k s ↔ y ∈ s ∨ ∃ z ∈ s, y ∈ kdeps k z := by
  unfold reachStep
  rw [List.mem_eraseDups, List.mem_append, List.mem_flatMap]

theorem kdeps_key {k : Kept} {z y : CmdId} (h : y ∈ kdeps k z) : z ∈ k.map Prod.fst := by
  unfold kdeps at h
  cases hz : k.get z with
  | none => rw [hz] at h; simp at h
  | some e => exact Kept.get_some_mem k z e hz

theorem reach_mono (k : Kept) (src : CmdId) (n m : Nat) (h : n ≤ m) (y : CmdId)
    (hy : y ∈ iter (reachStep k) n [src]) : y ∈ iter (reachStep k) m [src] := by
  induction h with
  | refl => exact hy
  | step _ ih => rw [iter_succ', reachStep_mem]; exact Or.inl ih

/-- The number of keys of `k` in `s`. -/
def keysIn (k : Kept) (s : List CmdId) : Nat :=
  ((k.map Prod.fst).filter (fun y => decide (y ∈ s))).length

theorem filter_length_le_of {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a → q a) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> simp
    · omega
    · omega
    · have := h a (List.mem_cons_self) hp; rw [hq] at this; cases this
    · omega

theorem filter_length_lt_of {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a → q a)
    (b : α) (hb : b ∈ l) (hpb : p b = false) (hqb : q b = true) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    have hle := filter_length_le_of l p q (fun c hc => h c (List.mem_cons_of_mem a hc))
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hpb, hqb]; simp; omega
    · have ih := ih (fun c hc => h c (List.mem_cons_of_mem a hc)) hb'
      cases hp : p a <;> cases hq : q a <;> simp
      · omega
      · omega
      · have := h a (List.mem_cons_self) hp; rw [hq] at this; cases this
      · omega

theorem keysIn_le (k : Kept) (s : List CmdId) : keysIn k s ≤ k.length := by
  unfold keysIn
  calc _ ≤ (k.map Prod.fst).length := List.length_filter_le _ _
    _ = k.length := List.length_map ..

/-- Some step adds no key: then the iteration is stable from the next step on. -/
theorem reach_stable_of (k : Kept) (src : CmdId) (n : Nat)
    (h : ∀ y ∈ k.map Prod.fst, y ∈ iter (reachStep k) (n + 1) [src] → y ∈ iter (reachStep k) n [src]) :
    ∀ m, ∀ y ∈ iter (reachStep k) m [src], y ∈ iter (reachStep k) (n + 1) [src] := by
  intro m
  induction m with
  | zero => intro y hy; exact reach_mono k src 0 (n + 1) (by omega) y hy
  | succ m ih =>
    intro y hy
    rw [iter_succ', reachStep_mem] at hy
    rcases hy with hy | ⟨z, hz, hyz⟩
    · exact ih y hy
    · have hz' := h z (kdeps_key hyz) (ih z hz)
      rw [iter_succ', reachStep_mem]
      exact Or.inr ⟨z, hz', hyz⟩

theorem reach_exists_stable (k : Kept) (src : CmdId) :
    ∃ n ≤ k.length, ∀ y ∈ k.map Prod.fst, y ∈ iter (reachStep k) (n + 1) [src] →
      y ∈ iter (reachStep k) n [src] := by
  apply Classical.byContradiction
  intro hno
  simp only [not_exists, not_and, Classical.not_forall] at hno
  have grow : ∀ n ≤ k.length, keysIn k (iter (reachStep k) n [src]) + 1 ≤
      keysIn k (iter (reachStep k) (n + 1) [src]) := by
    intro n hn
    obtain ⟨y, hyk, hy1, hy0⟩ := hno n hn
    unfold keysIn
    have := filter_length_lt_of (k.map Prod.fst)
      (fun y => decide (y ∈ iter (reachStep k) n [src]))
      (fun y => decide (y ∈ iter (reachStep k) (n + 1) [src]))
      (fun a _ ha => by
        simp only [decide_eq_true_eq] at ha ⊢
        exact reach_mono k src n (n + 1) (by omega) a ha)
      y hyk (by simpa using hy0) (by simpa using hy1)
    omega
  have : ∀ n ≤ k.length + 1, n ≤ keysIn k (iter (reachStep k) n [src]) := by
    intro n
    induction n with
    | zero => intro _; omega
    | succ n ih => intro hn; have := grow n (by omega); have := ih (by omega); omega
  have h1 := this (k.length + 1) (Nat.le_refl _)
  have h2 := keysIn_le k (iter (reachStep k) (k.length + 1) [src])
  omega

theorem reach_all_in_fuel (k : Kept) (src : CmdId) (m : Nat) (y : CmdId)
    (hy : y ∈ iter (reachStep k) m [src]) : y ∈ iter (reachStep k) (k.length + 1) [src] := by
  obtain ⟨n, hn, hst⟩ := reach_exists_stable k src
  rcases Nat.le_total m (k.length + 1) with hm | hm
  · exact reach_mono k src m _ hm y hy
  · exact reach_mono k src (n + 1) _ (by omega) y (reach_stable_of k src n hst m y hy)

theorem reach_iter_of_trans (k : Kept) (src y : CmdId)
    (h : Relation.TransGen (fun y d => d ∈ kdeps k y) src y) : ∃ m, y ∈ iter (reachStep k) m [src] := by
  induction h with
  | single h =>
    refine ⟨1, ?_⟩
    rw [iter_succ', reachStep_mem]
    exact Or.inr ⟨src, by simp [iter], h⟩
  | tail _ hbc ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, ?_⟩
    rw [iter_succ', reachStep_mem]
    exact Or.inr ⟨_, hm, hbc⟩

/-- **`recReaches` decides reachability** through the kept dependencies. -/
theorem recReaches_iff (k : Kept) (src dst : CmdId) :
    recReaches k src dst = true ↔ Relation.TransGen (fun y d => d ∈ kdeps k y) src dst := by
  refine ⟨recReaches_sound k src dst, fun h => ?_⟩
  rw [recReaches_eq, decide_eq_true_eq, List.mem_flatMap]
  cases h with
  | single h =>
    exact ⟨src, reach_mono k src 0 _ (by omega) src (by simp [iter]), h⟩
  | tail hab hbc =>
    obtain ⟨m, hm⟩ := reach_iter_of_trans k src _ hab
    exact ⟨_, reach_all_in_fuel k src m _ hm, hbc⟩

end sp

end Perennial.github_com.imdea_software.swiftpaxos

