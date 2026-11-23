/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/FillOrder.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Round N3 (sv-swc), item 4's order (pure):** `fillNewLeaderAckN`'s report is in the order
`upd_report`'s h8 asks for. The Go code (recovery.go:494-536) ranks each id by its first
position in `handled` plus one (`0` when not handled), sorts the entries' indices by
`(rank, index)` (`slices.SortFunc`, whose post gives a permutation in which no later element
is smaller), and takes the entries in that order. With the entries a permutation of the
sequence `B ++ H` of `cballot` (`localOk`: the base `B`, then `handled` `H`; without
duplicates), any such order is `B' ++ H` with `B'` a permutation of `B` (`swift.fill_order`): the
rank only increases along it, the base's ids have rank 0 and `handled`'s ids have distinct
positive ranks in `H`'s order. The index tie-break is not needed.
-/
module

public import Init

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos

variable {α : Type} [DecidableEq α]

/-- The rank `fillNewLeaderAckN` gives an id: its first position in `H` plus one, `0` if not
there. -/
def swift.hrank (H : List α) (y : α) : Nat := if y ∈ H then H.idxOf y + 1 else 0

/-- Along a list on which `f` only increases, the zeros of `f` come first. -/
theorem swift.split_zero (f : α → Nat) :
    ∀ L : List α, L.Pairwise (fun x y => f x ≤ f y) →
      L = L.filter (fun x => f x = 0) ++ L.filter (fun x => f x ≠ 0)
  | [], _ => rfl
  | a :: t, h => by
    have ht := swift.split_zero f t (List.pairwise_cons.mp h).2
    by_cases ha : f a = 0
    · simp only [List.filter_cons, ha, decide_true, if_true, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, if_false, List.cons_append]
      exact congrArg (a :: ·) ht
    · have hall : ∀ x ∈ t, f x ≠ 0 := fun x hx => by
        have := (List.pairwise_cons.mp h).1 x hx; omega
      have h0 : t.filter (fun x => f x = 0) = [] :=
        List.filter_eq_nil_iff.mpr (fun x hx => by simpa using hall x hx)
      have h1 : t.filter (fun x => f x ≠ 0) = t :=
        List.filter_eq_self.mpr (fun x hx => by simpa using hall x hx)
      simp only [List.filter_cons, ha, decide_false, Bool.false_eq_true, if_false, ne_eq,
        not_false_eq_true, decide_true, if_true, h0, h1, List.nil_append]

/-- Two permutations, both strictly increasing in `f`, are equal. -/
theorem swift.eq_of_perm_lt (f : α → Nat) :
    ∀ l1 l2 : List α, l1.Perm l2 → l1.Pairwise (fun x y => f x < f y) →
      l2.Pairwise (fun x y => f x < f y) → l1 = l2
  | [], l2, hp, _, _ => List.Perm.nil_eq hp
  | a :: t, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: t, b :: u, hp, h1, h2 => by
    have hab : a = b := by
      refine Classical.byContradiction fun hne => ?_
      have ha : a ∈ u := by
        have : a ∈ b :: u := hp.subset (List.mem_cons_self)
        rcases List.mem_cons.mp this with e | e
        · exact absurd e hne
        · exact e
      have hb : b ∈ t := by
        have : b ∈ a :: t := hp.symm.subset (List.mem_cons_self)
        rcases List.mem_cons.mp this with e | e
        · exact absurd e.symm hne
        · exact e
      have x1 := (List.pairwise_cons.mp h1).1 b hb
      have x2 := (List.pairwise_cons.mp h2).1 a ha
      omega
    subst hab
    rw [swift.eq_of_perm_lt f t u (List.Perm.cons_inv hp) (List.pairwise_cons.mp h1).2
      (List.pairwise_cons.mp h2).2]

theorem swift.hrank_cons_ne (a y : α) (t : List α) (hy : y ∈ t) (hne : y ≠ a) :
    swift.hrank (a :: t) y = swift.hrank t y + 1 := by
  unfold swift.hrank
  rw [if_pos (List.mem_cons_of_mem _ hy), if_pos hy, List.idxOf_cons]
  have : (a == y) = false := by simpa using (Ne.symm hne)
  rw [this]; rfl

/-- `handled` without duplicates is strictly increasing in its own rank. -/
theorem swift.hrank_pairwise : ∀ H : List α, H.Nodup → H.Pairwise (fun x y => swift.hrank H x < swift.hrank H y)
  | [], _ => List.Pairwise.nil
  | a :: t, hnd => by
    have hat : a ∉ t := (List.nodup_cons.mp hnd).1
    have ih := swift.hrank_pairwise t (List.nodup_cons.mp hnd).2
    have ha : swift.hrank (a :: t) a = 1 := by
      unfold swift.hrank; rw [if_pos List.mem_cons_self, List.idxOf_cons_self]
    have hpos : ∀ y ∈ t, 0 < swift.hrank t y := fun y hy => by
      unfold swift.hrank; rw [if_pos hy]; omega
    refine List.pairwise_cons.mpr ⟨fun y hy => ?_, ?_⟩
    · have hne : y ≠ a := fun e => hat (e ▸ hy)
      rw [ha, swift.hrank_cons_ne a y t hy hne]
      have := hpos y hy; omega
    · refine List.Pairwise.imp_of_mem ?_ ih
      intro x y hx hy hxy
      rw [swift.hrank_cons_ne a x t hx (fun e => hat (e ▸ hx)),
        swift.hrank_cons_ne a y t hy (fun e => hat (e ▸ hy))]
      omega

theorem swift.hrank_inj (H : List α) (x y : α) (hx : x ∈ H) (hy : y ∈ H)
    (h : swift.hrank H x = swift.hrank H y) : x = y := by
  unfold swift.hrank at h
  rw [if_pos hx, if_pos hy] at h
  have h' : H.idxOf x = H.idxOf y := by omega
  have e1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)
  have e2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)
  rw [← e1, ← e2]
  simp only [h']

/-- **The report's order** (see the file header): entries `L`, a permutation of `B ++ H` (no
duplicates), along which the rank in `H` only increases, are `B' ++ H` with `B' ~ B`. -/
theorem swift.fill_order (B H L : List α) (hnd : (B ++ H).Nodup) (hp : L.Perm (B ++ H))
    (hs : L.Pairwise (fun x y => swift.hrank H x ≤ swift.hrank H y)) :
    ∃ B', B'.Perm B ∧ L = B' ++ H := by
  have hdisj : ∀ x ∈ B, x ∉ H := fun x hx hxH =>
    (List.nodup_append.mp hnd).2.2 x hx x hxH rfl
  have hB0 : B.filter (fun x => swift.hrank H x = 0) = B :=
    List.filter_eq_self.mpr (fun x hx => by simp [swift.hrank, hdisj x hx])
  have hB1 : B.filter (fun x => swift.hrank H x ≠ 0) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by simp [swift.hrank, hdisj x hx])
  have hH0 : H.filter (fun x => swift.hrank H x = 0) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by simp [swift.hrank, hx])
  have hH1 : H.filter (fun x => swift.hrank H x ≠ 0) = H :=
    List.filter_eq_self.mpr (fun x hx => by simp [swift.hrank, hx])
  have hsplit := swift.split_zero (swift.hrank H) L hs
  refine ⟨L.filter (fun x => swift.hrank H x = 0), ?_, ?_⟩
  · have := hp.filter (fun x => swift.hrank H x = 0)
    rw [List.filter_append, hB0, hH0, List.append_nil] at this
    exact this
  · have hp1 := hp.filter (fun x => swift.hrank H x ≠ 0)
    rw [List.filter_append, hB1, hH1, List.nil_append] at hp1
    have hHnd : H.Nodup := (List.nodup_append.mp hnd).2.1
    have hLnd : L.Nodup := hp.nodup_iff.mpr hnd
    have hs1 : (L.filter (fun x => swift.hrank H x ≠ 0)).Pairwise
        (fun x y => swift.hrank H x < swift.hrank H y) := by
      have hsub := (List.filter_sublist (p := fun x => decide (swift.hrank H x ≠ 0)) (l := L))
      have hnd1 : (L.filter (fun x => swift.hrank H x ≠ 0)).Nodup := hLnd.sublist hsub
      have hle := hs.sublist hsub
      refine (hle.and hnd1).imp_of_mem ?_
      intro x y hx hy ⟨hxy, hne⟩
      have hxH : x ∈ H := hp1.subset hx
      have hyH : y ∈ H := hp1.subset hy
      rcases Nat.lt_or_eq_of_le hxy with h | h
      · exact h
      · exact absurd (swift.hrank_inj H x y hxH hyH h) hne
    have hH := swift.eq_of_perm_lt (swift.hrank H) _ _ hp1 hs1 (swift.hrank_pairwise H hHnd)
    have h2 := hsplit
    rw [hH] at h2
    exact h2

end Perennial.github_com.imdea_software.swiftpaxos
