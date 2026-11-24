/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLa/Count.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-a: Go maps as sorted association lists: `put`/`del` keep them sorted, and the count of
entries satisfying a predicate changes only at the key written.
-/
module

public import Dsverify.Proof.gryff.Model.Types

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.La

open model

variable {n : Nat} {V : Type}

/-- Keys strictly increasing (the canonical form of a Go map). -/
def Srt (m : AMap n V) : Prop := m.Pairwise (fun a b => a.1.toNat < b.1.toNat)

/-- The number of entries whose value satisfies `f`. -/
def cnt (f : V → Bool) (m : AMap n V) : Nat := m.countP (fun e => f e.2)

/-- The count of an optional value. -/
def g1 (f : V → Bool) : Option V → Nat
  | some v => if f v then 1 else 0
  | none => 0

theorem mem_put' {m : AMap n V} {k : BitVec n} {v : V} {e : BitVec n × V}
    (h : e ∈ m.put k v) : e = (k, v) ∨ e ∈ m := by
  induction m with
  | nil => simp [AMap.put] at h; exact Or.inl h
  | cons x t ih =>
    obtain ⟨k0, v0⟩ := x
    unfold AMap.put at h
    split at h
    · simp at h; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
    · split at h
      · simp at h; rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
        · exact Or.inr (by simp [h])
      · simp at h; rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by simp [h'])

theorem srt_put {m : AMap n V} (hm : Srt m) (k : BitVec n) (v : V) : Srt (m.put k v) := by
  induction m with
  | nil => simp [AMap.put, Srt]
  | cons x t ih =>
    obtain ⟨k0, v0⟩ := x
    unfold Srt at hm
    rw [List.pairwise_cons] at hm
    unfold AMap.put
    split
    · rename_i h; subst h
      unfold Srt; rw [List.pairwise_cons]; exact hm
    · split
      · rename_i h1 h2
        unfold Srt; rw [List.pairwise_cons]
        refine ⟨?_, List.pairwise_cons.2 hm⟩
        intro b hb; simp at hb
        rcases hb with rfl | hb
        · exact h2
        · exact Nat.lt_trans h2 (hm.1 b hb)
      · rename_i h1 h2
        unfold Srt; rw [List.pairwise_cons]
        refine ⟨?_, ih hm.2⟩
        intro b hb
        rcases mem_put' hb with rfl | hb
        · have : k.toNat ≠ k0.toNat := fun e => h1 (BitVec.eq_of_toNat_eq e)
          show k0.toNat < k.toNat
          omega
        · exact hm.1 b hb

theorem srt_del {m : AMap n V} (hm : Srt m) (k : BitVec n) : Srt (m.del k) :=
  List.Pairwise.sublist List.filter_sublist hm

theorem get?_lt {k0 : BitVec n} {v0 : V} {t : AMap n V} (hm : Srt ((k0, v0) :: t)) {k : BitVec n}
    (hk : k.toNat < k0.toNat) : AMap.get? ((k0, v0) :: t) k = none := by
  unfold AMap.get?
  rw [List.lookup_eq_none_iff]
  intro p hp
  unfold Srt at hm
  rw [List.pairwise_cons] at hm
  simp at hp
  rcases hp with rfl | hp
  · simp; intro e; subst e; omega
  · have := hm.1 p hp; simp only at this; simp; intro e; subst e; omega

theorem get?_cons_ne {k0 : BitVec n} {v0 : V} {t : AMap n V} {k : BitVec n} (h : k ≠ k0) :
    AMap.get? ((k0, v0) :: t) k = AMap.get? t k := by
  have : (k == k0) = false := by simp [h]
  simp [AMap.get?, List.lookup, this]

theorem get?_cons_eq {k0 : BitVec n} {v0 : V} {t : AMap n V} :
    AMap.get? ((k0, v0) :: t) k0 = some v0 := by
  simp [AMap.get?, List.lookup]

theorem cnt_cons (f : V → Bool) (k : BitVec n) (v : V) (t : AMap n V) :
    cnt f ((k, v) :: t) = cnt f t + g1 f (some v) := by
  simp only [cnt, List.countP_cons, g1]

theorem cnt_put (f : V → Bool) {m : AMap n V} (hm : Srt m) (k : BitVec n) (v : V) :
    cnt f (m.put k v) + g1 f (m.get? k) = cnt f m + g1 f (some v) := by
  induction m with
  | nil => simp [AMap.put, AMap.get?, cnt, g1, List.lookup]
  | cons x t ih =>
    obtain ⟨k0, v0⟩ := x
    have hm' := hm
    unfold Srt at hm
    rw [List.pairwise_cons] at hm
    unfold AMap.put
    split
    · rename_i h; subst h
      rw [get?_cons_eq, cnt_cons, cnt_cons]; omega
    · rename_i h1
      split
      · rename_i h2
        rw [get?_lt hm' h2, cnt_cons]; simp [g1]
      · rw [get?_cons_ne h1, cnt_cons, cnt_cons]
        have := ih hm.2
        omega

theorem filter_ne_self {k0 : BitVec n} {v0 : V} {t : AMap n V} (hm : Srt ((k0, v0) :: t)) :
    t.filter (fun e => e.1 != k0) = t := by
  unfold Srt at hm
  rw [List.pairwise_cons] at hm
  rw [List.filter_eq_self]
  intro p hp
  have := hm.1 p hp
  simp only at this
  simp only [bne_iff_ne, ne_eq]
  intro e; rw [e] at this; omega

theorem cnt_del (f : V → Bool) {m : AMap n V} (hm : Srt m) (k : BitVec n) :
    cnt f (m.del k) + g1 f (m.get? k) = cnt f m := by
  induction m with
  | nil => simp [AMap.del, AMap.get?, cnt, g1, List.lookup]
  | cons x t ih =>
    obtain ⟨k0, v0⟩ := x
    have hm' := hm
    unfold Srt at hm
    rw [List.pairwise_cons] at hm
    by_cases h : k0 = k
    · subst h
      have e1 : AMap.del ((k0, v0) :: t) k0 = t := by
        unfold AMap.del; rw [List.filter_cons]
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
        exact filter_ne_self hm'
      rw [e1, get?_cons_eq, cnt_cons]
    · have e1 : AMap.del ((k0, v0) :: t) k = (k0, v0) :: AMap.del t k := by
        unfold AMap.del; rw [List.filter_cons]
        have : (k0 != k) = true := by simp [h]
        simp only [this, if_true]
      rw [e1, get?_cons_ne (Ne.symm h), cnt_cons, cnt_cons]
      have := ih hm.2
      omega

end Perennial.gryff.pure.La
