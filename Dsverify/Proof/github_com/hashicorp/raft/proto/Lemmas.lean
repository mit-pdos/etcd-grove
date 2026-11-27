/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Lemmas.lean (241f27e).
-/
/-
`proto` — a small library of facts about logs (`ent`, `termAt`, `agree`, `take`, `++`), point
updates, `LMok` of prefixes and under leader-log growth, and quorum intersection.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Model

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ### `if` (the core `if_pos`/`if_neg` are deprecated here) -/

theorem if_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem if_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-! ### Point updates -/

@[simp] theorem upd_same {α : Type} (f : SID → α) (i : SID) (a : α) : upd f i a i = a := by
  simp [upd]

@[simp] theorem upd_ne {α : Type} (f : SID → α) (i j : SID) (a : α) (h : j ≠ i) :
    upd f i a j = f j := by
  simp [upd, h]

theorem upd_apply {α : Type} (f : SID → α) (i j : SID) (a : α) :
    upd f i a j = if j = i then a else f j := rfl

@[simp] theorem updT_same {α : Type} (f : Nat → α) (t : Nat) (a : α) : updT f t a t = a := by
  simp [updT]

@[simp] theorem updT_ne {α : Type} (f : Nat → α) (t u : Nat) (a : α) (h : u ≠ t) :
    updT f t a u = f u := by
  simp [updT, h]

theorem updT_apply {α : Type} (f : Nat → α) (t u : Nat) (a : α) :
    updT f t a u = if u = t then a else f u := rfl

theorem updST_apply {α : Type} (f : SID → Nat → α) (i : SID) (t : Nat) (a : α) (j : SID) (u : Nat) :
    updST f i t a j u = if j = i ∧ u = t then a else f j u := rfl

/-! ### `ent` and `termAt` -/

@[simp] theorem ent_zero (L : RLog) : ent L 0 = none := by simp [ent]

theorem ent_succ (L : RLog) (k : Nat) : ent L (k + 1) = L[k]? := by simp [ent]

theorem ent_eq_none_iff (L : RLog) (k : Nat) : ent L k = none ↔ k = 0 ∨ L.length < k := by
  unfold ent
  split <;> simp_all
  omega

theorem ent_isSome (L : RLog) (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ L.length) :
    ∃ e, ent L k = some e := by
  unfold ent
  split
  · omega
  · exact ⟨L[k - 1], by simp⟩

theorem ent_le_length {L : RLog} {k : Nat} {e : Entry} (h : ent L k = some e) :
    1 ≤ k ∧ k ≤ L.length := by
  unfold ent at h
  split at h
  · simp at h
  · have := (List.getElem?_eq_some_iff.mp h).1
    omega

theorem termAt_of_ent {L : RLog} {k : Nat} {e : Entry} (h : ent L k = some e) : termAt L k = e.term := by
  simp [termAt, h]

@[simp] theorem termAt_zero (L : RLog) : termAt L 0 = 0 := by simp [termAt]

theorem termAt_gt (L : RLog) (k : Nat) (h : L.length < k) : termAt L k = 0 := by
  have : ent L k = none := (ent_eq_none_iff L k).mpr (Or.inr h)
  simp [termAt, this]

theorem ent_take (L : RLog) (n k : Nat) (h : k ≤ n) : ent (L.take n) k = ent L k := by
  unfold ent
  split
  · rfl
  · rw [List.getElem?_take]; simp; omega

theorem termAt_take (L : RLog) (n k : Nat) (h : k ≤ n) : termAt (L.take n) k = termAt L k := by
  simp [termAt, ent_take L n k h]

theorem ent_append_left (L X : RLog) (k : Nat) (h : k ≤ L.length) : ent (L ++ X) k = ent L k := by
  unfold ent
  split
  · rfl
  · rw [List.getElem?_append_left (by omega)]

theorem termAt_append_left (L X : RLog) (k : Nat) (h : k ≤ L.length) :
    termAt (L ++ X) k = termAt L k := by
  simp [termAt, ent_append_left L X k h]

theorem ent_append_right (L X : RLog) (k : Nat) (h : L.length < k) :
    ent (L ++ X) k = ent X (k - L.length) := by
  unfold ent
  split
  · omega
  · split
    · omega
    · rw [List.getElem?_append_right (by omega)]
      congr 1
      omega

theorem termAt_append_right (L X : RLog) (k : Nat) (h : L.length < k) :
    termAt (L ++ X) k = termAt X (k - L.length) := by
  simp [termAt, ent_append_right L X k h]

theorem ent_drop (L : RLog) (p k : Nat) (h : 1 ≤ k) : ent (L.drop p) k = ent L (p + k) := by
  unfold ent
  split
  · omega
  · split
    · omega
    · rw [List.getElem?_drop]
      congr 1
      omega

theorem termAt_drop (L : RLog) (p k : Nat) (h : 1 ≤ k) : termAt (L.drop p) k = termAt L (p + k) := by
  simp [termAt, ent_drop L p k h]

theorem lastTerm_take (L : RLog) (n : Nat) (h : n ≤ L.length) :
    lastTerm (L.take n) = termAt L n := by
  unfold lastTerm
  rw [List.length_take, Nat.min_eq_left h, termAt_take _ _ _ (Nat.le_refl _)]

/-! ### `agree` -/

theorem agree_zero (A B : RLog) : agree A B 0 := by simp [agree]

theorem agree_refl (A : RLog) (k : Nat) (h : k ≤ A.length) : agree A A k := ⟨h, h, rfl⟩

theorem agree_symm {A B : RLog} {k : Nat} (h : agree A B k) : agree B A k :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem agree_trans {A B C : RLog} {k : Nat} (h1 : agree A B k) (h2 : agree B C k) : agree A C k :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

theorem agree_mono {A B : RLog} {k j : Nat} (h : agree A B k) (hj : j ≤ k) : agree A B j := by
  refine ⟨by have := h.1; omega, by have := h.2.1; omega, ?_⟩
  have e := congrArg (List.take j) h.2.2
  simp only [List.take_take, Nat.min_eq_left hj] at e
  exact e

theorem agree_ent {A B : RLog} {k x : Nat} (h : agree A B k) (hx : x ≤ k) : ent A x = ent B x := by
  rw [← ent_take A k x hx, ← ent_take B k x hx, h.2.2]

theorem agree_termAt {A B : RLog} {k x : Nat} (h : agree A B k) (hx : x ≤ k) :
    termAt A x = termAt B x := by
  simp [termAt, agree_ent h hx]

theorem agree_append_left {A B : RLog} (X : RLog) {k : Nat} (h : agree A B k) : agree (A ++ X) B k := by
  refine ⟨by simp; have := h.1; omega, h.2.1, ?_⟩
  rw [List.take_append_of_le_length h.1]
  exact h.2.2

theorem agree_append_right {A B : RLog} (X : RLog) {k : Nat} (h : agree A B k) : agree A (B ++ X) k :=
  agree_symm (agree_append_left X (agree_symm h))

theorem agree_of_prefix {A B : RLog} {k : Nat} (h : A <+: B) (hk : k ≤ A.length) : agree A B k := by
  obtain ⟨X, rfl⟩ := h
  exact agree_append_right X (agree_refl A k hk)

theorem agree_prefix_right {A B B' : RLog} {k : Nat} (h : agree A B k) (hp : B <+: B') : agree A B' k := by
  obtain ⟨X, rfl⟩ := hp
  exact agree_append_right X h

theorem agree_prefix_left {A A' B : RLog} {k : Nat} (h : agree A B k) (hp : A <+: A') : agree A' B k :=
  agree_symm (agree_prefix_right (agree_symm h) hp)

theorem agree_take_left {A B : RLog} {k : Nat} (n : Nat) (h : agree A B k) (hk : k ≤ n) :
    agree (A.take n) B k := by
  refine ⟨by simp; have := h.1; omega, h.2.1, ?_⟩
  rw [List.take_take, Nat.min_eq_left hk]
  exact h.2.2

theorem agree_take_self (A : RLog) {k n : Nat} (hk : k ≤ n) (hA : k ≤ A.length) :
    agree (A.take n) A k :=
  agree_take_left n (agree_refl A k hA) hk

theorem agree_of_take {A B : RLog} {k n : Nat} (h : agree (A.take n) B k) : agree A B k := by
  have h1 := h.1
  simp only [List.length_take] at h1
  refine ⟨by omega, h.2.1, ?_⟩
  have := h.2.2
  rw [List.take_take, Nat.min_eq_left (by omega)] at this
  exact this

/-- Two logs agree up to `k` iff they agree at every index `1..k`. -/
theorem agree_of_ent {A B : RLog} {k : Nat} (hA : k ≤ A.length) (hB : k ≤ B.length)
    (h : ∀ x, 1 ≤ x → x ≤ k → ent A x = ent B x) : agree A B k := by
  refine ⟨hA, hB, ?_⟩
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_take, List.getElem?_take]
  split
  · have := h (n + 1) (by omega) (by omega)
    simpa [ent_succ] using this
  · rfl

/-! ### Prefixes -/

theorem prefix_take_of_agree {A B : RLog} (h : agree A B A.length) : A <+: B := by
  have := h.2.2
  rw [List.take_length] at this
  rw [this]
  exact List.take_prefix _ _

/-! ### `LMok` -/

theorem LMok_take {σ : PState} {L : RLog} (h : LMok σ L) (n : Nat) : LMok σ (L.take n) := by
  intro k hk1 hk2
  simp only [List.length_take] at hk2
  rw [termAt_take _ _ _ (by omega)]
  exact agree_take_left n (h k hk1 (by omega)) (by omega)

theorem LMok_prefix {σ : PState} {L L' : RLog} (h : LMok σ L) (hp : L' <+: L) : LMok σ L' := by
  rw [List.prefix_iff_eq_take.mp hp]
  exact LMok_take h _

theorem LMok_mono {σ σ' : PState} {L : RLog} (hg : ∀ t, σ.llog t <+: σ'.llog t) (h : LMok σ L) :
    LMok σ' L := by
  intro k hk1 hk2
  exact agree_prefix_right (h k hk1 hk2) (hg _)

/-- In an `LMok` log, the term of an entry at `k ≥ 1` is the term of the leader log at `k`. -/
theorem LMok_termAt {σ : PState} {L : RLog} (h : LMok σ L) {k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ L.length) :
    k ≤ (σ.llog (termAt L k)).length ∧ termAt (σ.llog (termAt L k)) k = termAt L k := by
  have a := h k hk1 hk2
  exact ⟨a.2.1, (agree_termAt a (Nat.le_refl _)).symm⟩

/-- Two `LMok` logs with the same term at `n ≥ 1` agree up to `n`. -/
theorem LMok_agree {σ : PState} {A B : RLog} (hA : LMok σ A) (hB : LMok σ B) {n : Nat}
    (h1 : 1 ≤ n) (hnA : n ≤ A.length) (hnB : n ≤ B.length) (ht : termAt A n = termAt B n) :
    agree A B n := by
  have a := hA n h1 hnA
  have b := hB n h1 hnB
  rw [ht] at a
  exact agree_trans a (agree_symm b)

/-! ### Quorums -/

/-- Two quorums of one configuration meet (stage 4: of the voters `V`, not of the fixed voters). -/
theorem quorum_inter {V Q1 Q2 : List SID} (h1 : isQuorumOf V Q1) (h2 : isQuorumOf V Q2) :
    ∃ j, j ∈ Q1 ∧ j ∈ Q2 := by
  apply Classical.byContradiction
  intro hn
  have hd : ∀ a, a ∈ Q1 → ∀ b, b ∈ Q2 → a ≠ b := by
    intro a ha b hb hab
    subst hab
    exact hn ⟨a, ha, hb⟩
  have hnd : (Q1 ++ Q2).Nodup := List.nodup_append.mpr ⟨h1.1, h2.1, hd⟩
  have hsub : Q1 ++ Q2 ⊆ V := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h1.2.1 x hx
    · exact h2.2.1 x hx
  have := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_append] at this
  have := h1.2.2
  have := h2.2.2
  omega

/- stage-4 interface: `isQuorum σ` (a majority of the fixed voters) is gone (quorums are of a
configuration, `isQuorumOf V`, which does not depend on the state); proved at stage3-final:
theorem isQuorum_congr {σ σ' : PState} {Q : List SID} (hv : σ'.voters = σ.voters) (h : isQuorum σ Q) :
    isQuorum σ' Q := by
  unfold isQuorum; rw [hv]; exact h
-/

end proto
end github_com.hashicorp.raft
end Perennial
