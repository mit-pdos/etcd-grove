/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumPure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The pure model of `replica/quorum.go`'s quorum system without a quorum file (the deployment's
`config.plain`: `conf.Quorum = ""`): the quorums of `N / 2 + 1` replicas in `subsets`'
enumeration order (`qcomb`), each leader's list of them (`lqs`), the fast quorum of a ballot
(`aqOf`), and the facts the specs' proofs need (no division by zero: every leader of a
non-negative ballot has a quorum; the int32 conversions are exact for `N ≤ 7`).

`qcomb` is a local copy of `Spec/swift/Model.lean`'s `combos` (that file is being rewritten; the
relation is `QuorumModel.lean`'s, nothing else depends on it).
-/
module

public import Perennial.Std.Word.LittleEndian

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace replica.quorum

/-- The `k`-element sublists of `l`, in the lexicographic order of the chosen indices. -/
def qcomb : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: l => (qcomb k l).map (a :: ·) ++ qcomb (k + 1) l

/-- What `subsets(ids, N, k, i, q, ...)` emits (the sets `q` holds when `quorumSize == 0`), in
order: nothing for `k < 0`, else `q` extended by each `k`-subset of `[i, N)`. -/
def emitL (N : Nat) (k : Int) (i : Nat) (q : List Nat) : List (List Nat) :=
  if k < 0 then [] else (qcomb k.toNat (List.range' i (N - i))).map (q ++ ·)

/-- The quorums (`N / 2 + 1` replicas) in `subsets`' order. -/
def quorums (N : Nat) : List (List Nat) := qcomb (N / 2 + 1) (List.range N)

/-- Leader `l`'s fast quorums (`qs[l]`, by `qid`). -/
def lqs (N l : Nat) : List (List Nat) := (quorums N).filter (fun s => decide (l ∈ s))

/-- The number of leader `l`'s fast quorums (`NumAQ`). -/
def numAQ (N l : Nat) : Nat := (lqs N l).length

/-- The fast quorum of the non-negative ballot `b` (`AQ`). -/
def aqOf (N b : Nat) : List Nat :=
  (lqs N (b % N)).getD ((b / N) % numAQ N (b % N)) []

theorem sint_W32 (x : Int) (h0 : -2^31 ≤ x) (h1 : x < 2^31) : sint.Z (W32 x) = x := by word
theorem sint_W64 (x : Int) (h0 : -2^63 ≤ x) (h1 : x < 2^63) : sint.Z (W64 x) = x := by word

/-! ## The recursion of `subsets` -/

theorem flatMap_congr' {α β : Type} {f g : α → List β} {l : List α}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem qcomb_succ_range' (K i n : Nat) :
    qcomb (K + 1) (List.range' i n) =
      (List.range' i n).flatMap
        (fun j => (qcomb K (List.range' (j + 1) (n - (j + 1 - i)))).map (j :: ·)) := by
  induction n generalizing i with
  | zero => simp [qcomb]
  | succ n ih =>
    rw [List.range'_succ, qcomb, ih (i + 1)]
    simp only [List.flatMap_cons]
    congr 1
    · congr 3; omega
    · apply flatMap_congr'
      intro j hj
      rw [List.mem_range'_1] at hj
      congr 3; omega

/-- `subsets`' unfolding: emit `q` when `k = 0`, then recurse on each `j ∈ [i, N)`. -/
theorem emitL_unfold (N : Nat) (k : Int) (i : Nat) (q : List Nat) :
    emitL N k i q = (if k = 0 then [q] else []) ++
      (List.range' i (N - i)).flatMap (fun j => emitL N (k - 1) (j + 1) (q ++ [j])) := by
  unfold emitL
  by_cases hk : k < 0
  · simp only [hk, ite_true, show k ≠ 0 by omega, ite_false, List.nil_append]
    simp [show k - 1 < 0 by omega]
  simp only [hk, ite_false]
  by_cases h0 : k = 0
  · subst h0
    simp only [Int.toNat_zero, qcomb, List.map_cons, List.append_nil, List.map_nil, ite_true,
      show ((0 : Int) - 1 < 0) by omega]
    rw [flatMap_congr' (g := fun _ => []) (fun _ _ => rfl)]
    simp
  · simp only [h0, ite_false, List.nil_append, show ¬ (k - 1 < 0) by omega]
    obtain ⟨K, hK⟩ : ∃ K : Nat, k.toNat = K + 1 := ⟨k.toNat - 1, by omega⟩
    have hK1 : (k - 1).toNat = K := by omega
    rw [hK, hK1, qcomb_succ_range', List.map_flatMap]
    apply flatMap_congr'
    intro j hj
    rw [List.mem_range'_1] at hj
    rw [List.map_map, show N - i - (j + 1 - i) = N - (j + 1) by omega]
    apply List.map_congr_left
    intro s _
    simp

/-! ## Facts of the enumeration -/

theorem mem_qcomb (k : Nat) (l s : List Nat) (h : s ∈ qcomb k l) :
    s.length = k ∧ s.Sublist l := by
  induction l generalizing k s with
  | nil =>
    cases k with
    | zero => simp [qcomb] at h; subst h; simp
    | succ k => simp [qcomb] at h
  | cons a l ih =>
    cases k with
    | zero => simp [qcomb] at h; subst h; simp
    | succ k =>
      simp only [qcomb, List.mem_append, List.mem_map] at h
      rcases h with ⟨t, ht, rfl⟩ | h
      · obtain ⟨h1, h2⟩ := ih k t ht
        exact ⟨by simp [h1], h2.cons_cons a⟩
      · obtain ⟨h1, h2⟩ := ih (k + 1) s h
        exact ⟨h1, h2.cons a⟩

/-- The emitted sets: `q` extended by sorted, distinct elements of `[i, N)`. -/
theorem mem_emitL (N : Nat) (k : Int) (i : Nat) (q s : List Nat) (h : s ∈ emitL N k i q) :
    ∃ t, s = q ++ t ∧ t.Sublist (List.range' i (N - i)) := by
  unfold emitL at h
  split at h
  · simp at h
  · simp only [List.mem_map] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨t, rfl, (mem_qcomb _ _ _ ht).2⟩

theorem mem_quorums (N : Nat) (s : List Nat) (h : s ∈ quorums N) :
    s.length = N / 2 + 1 ∧ s.Nodup ∧ ∀ x ∈ s, x < N := by
  obtain ⟨h1, h2⟩ := mem_qcomb _ _ _ h
  refine ⟨h1, h2.nodup (List.nodup_range), fun x hx => ?_⟩
  have := h2.subset hx
  simpa using this

theorem quorums_emitL (N : Nat) : emitL N ((N / 2 + 1 : Nat) : Int) 0 [] = quorums N := by
  unfold emitL quorums
  simp only [show ¬ (((N / 2 + 1 : Nat) : Int) < 0) by omega, ite_false, Int.toNat_natCast,
    Nat.sub_zero, List.nil_append, List.map_id', List.range_eq_range']

/-- Leader `l`'s quorums contain `l`. -/
theorem mem_lqs (N l : Nat) (s : List Nat) (h : s ∈ lqs N l) :
    s ∈ quorums N ∧ l ∈ s := by
  unfold lqs at h
  simp only [List.mem_filter, decide_eq_true_eq] at h
  exact h

/-- Every replica of a configuration of 1 to 7 replicas leads at least one fast quorum, and at
most 35 (so `NumAQ` is positive: `AQ` does not divide by zero, and fits an int32). -/
theorem numAQ_pos (N l : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (hl : l < N) :
    0 < numAQ N l ∧ numAQ N l ≤ 35 := by
  have key : ∀ N, N < 8 → ∀ l, l < N →
      0 < numAQ N l ∧ numAQ N l ≤ 35 := by
    unfold numAQ lqs quorums; decide
  exact key N (by omega) l hl

theorem quorums_length (N : Nat) (hN : N ≤ 7) : (quorums N).length ≤ 35 := by
  have key : ∀ N, N < 8 → (quorums N).length ≤ 35 := by unfold quorums; decide
  exact key N (by omega)

theorem aqOf_mem (N b : Nat) (hN : 1 ≤ N ∧ N ≤ 7) :
    aqOf N b ∈ lqs N (b % N) := by
  unfold aqOf
  have h := (numAQ_pos N (b % N) hN (Nat.mod_lt _ (by omega))).1
  have hlt : (b / N) % numAQ N (b % N) < (lqs N (b % N)).length := Nat.mod_lt _ h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact List.getElem_mem hlt

/-- The fast quorum of a ballot: `N / 2 + 1` distinct replicas, among them the ballot's
leader. -/
theorem aqOf_ok (N b : Nat) (hN : 1 ≤ N ∧ N ≤ 7) :
    (aqOf N b).length = N / 2 + 1 ∧ (aqOf N b).Nodup ∧ (∀ x ∈ aqOf N b, x < N) ∧
      b % N ∈ aqOf N b := by
  obtain ⟨h1, h2⟩ := mem_lqs _ _ _ (aqOf_mem N b hN)
  exact ⟨(mem_quorums _ _ h1).1, (mem_quorums _ _ h1).2.1, (mem_quorums _ _ h1).2.2, h2⟩

end replica.quorum

end Perennial.github_com.imdea_software.swiftpaxos

end
