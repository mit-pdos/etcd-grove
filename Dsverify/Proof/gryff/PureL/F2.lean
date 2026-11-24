/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/F2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: **F2** (`lin_prefix`): the linearization at a cut is a prefix of the one at a later cut.
From `front_mono` and L1 (`l1_cut`): every operation newly in `lin l k'` sorts after all of
`lin l k`'s.
-/
module

public import Dsverify.Proof.gryff.PureL.L1

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

theorem placeLe_iff {l : List Label} {o : Op} {f : PTag} :
    placeLe l o f = true ↔ ∃ t, place l o = some t ∧ tagLe t.toP f := by
  unfold placeLe
  cases place l o <;> simp

/-- The order of `lin` between an older operation (`a`, in `lin l k`) and a newly linearized one. -/
theorem opLe_new {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {k : Nat}
    {a b : Op} (hb : b ∈ ops l) {ta tb : model.Tag} (hta : place l a = some ta)
    (htb : place l b = some tb) (hag : a.g < k) (hal : tagLe ta.toP (front l k))
    (hnew : k ≤ b.g ∨ ¬ tagLe tb.toP (front l k)) :
    opLe l a b = true ∧ opLe l b a = false := by
  rw [opLe_eq, opLe_eq, hta, htb]
  simp only [Option.map_some, Option.getD_some]
  have hra := Op.rank_le a; have hrb := Op.rank_le b
  -- the facts as tag relations
  have key : tagLt ta.toP tb.toP ∨
      (ta.toP = tb.toP ∧ (a.rank < b.rank ∨ (a.rank = b.rank ∧ a.g < b.g))) := by
    rcases hnew with hg | hn
    · obtain ⟨h1, h2⟩ := l1_cut h hb htb hg
      by_cases hbl : tagLe tb.toP (front l k)
      · have heq : tb.toP = front l k := tagLe_antisymm hbl h1
        have hrb1 : b.rank ≠ 0 := fun h0 => tagLt_ne (h2 h0) heq.symm
        rcases hal with hlt | heq'
        · left; rw [heq]; exact hlt
        · right; refine ⟨heq'.trans heq.symm, ?_⟩; omega
      · left; exact tagLt_of_le_of_lt hal ((not_tagLe_iff _ _).1 hbl)
    · left; exact tagLt_of_le_of_lt hal ((not_tagLe_iff _ _).1 hn)
  generalize ta.toP = x at key; generalize tb.toP = y at key
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y
  have e1 := pureL.lexB_iff (x1, x2, x3) (y1, y2, y3) a.rank b.rank a.g b.g
  have e2 := pureL.lexB_iff (y1, y2, y3) (x1, x2, x3) b.rank a.rank b.g a.g
  simp only [tagLt, Prod.mk.injEq] at key e1 e2
  constructor
  · rw [e1]; omega
  · cases hh : pureL.lexB (y1, y2, y3) (x1, x2, x3) b.rank a.rank b.g a.g
    · rfl
    · rw [hh] at e2; have := e2.1 rfl; omega

/-- **F2** over any run (no hypothesis on clients; cuts anywhere). -/
theorem lin_prefix_run {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {k k' : Nat}
    (hkk : k ≤ k') : lin l k <+: lin l k' := by
  unfold lin
  let P : Op → Bool := fun o => decide (o.g < k) && placeLe l o (front l k)
  let P' : Op → Bool := fun o => decide (o.g < k') && placeLe l o (front l k')
  have hPP : ∀ o, P o = true → P' o = true := by
    intro o ho
    simp only [P, P', Bool.and_eq_true, decide_eq_true_eq, placeLe_iff] at ho ⊢
    obtain ⟨h1, t, ht, hle⟩ := ho
    exact ⟨by omega, t, ht, tagLe_trans hle (front_mono h hkk)⟩
  have hA : ((ops l).filter P').filter P = (ops l).filter P := by
    rw [List.filter_filter]
    apply List.filter_congr; intro o _
    cases hp : P o
    · simp
    · simp [hPP o hp]
  have hperm : ((ops l).filter P').Perm ((ops l).filter P ++ ((ops l).filter P').filter (fun o => !P o)) := by
    have := List.filter_append_perm P ((ops l).filter P')
    rw [hA] at this; exact this.symm
  show ((ops l).filter P).mergeSort (opLe l) <+: ((ops l).filter P').mergeSort (opLe l)
  have hanti : ∀ a ∈ (ops l).filter P', ∀ b ∈ (ops l).filter P', opLe l a b = true →
      opLe l b a = true → a = b := fun a ha b hb =>
    opLe_antisymm (List.mem_filter.1 ha).1 (List.mem_filter.1 hb).1
  have hord : ∀ a ∈ (ops l).filter P, ∀ b ∈ ((ops l).filter P').filter (fun o => !P o),
      opLe l a b = true ∧ ¬ opLe l b a = true := by
    intro a ha b hb
    obtain ⟨_, hPa⟩ := List.mem_filter.1 ha
    obtain ⟨hb1, hPb⟩ := List.mem_filter.1 hb
    obtain ⟨hbo, hP'b⟩ := List.mem_filter.1 hb1
    simp only [P, P', Bool.and_eq_true, decide_eq_true_eq, placeLe_iff, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at hPa hPb hP'b
    obtain ⟨hag, ta, hta, hal⟩ := hPa
    obtain ⟨-, tb, htb, -⟩ := hP'b
    have hnew : k ≤ b.g ∨ ¬ tagLe tb.toP (front l k) := by
      rcases hPb with h1 | h1
      · left; omega
      · right; intro hle
        have : placeLe l b (front l k) = true := placeLe_iff.2 ⟨tb, htb, hle⟩
        rw [this] at h1; cases h1
    obtain ⟨r1, r2⟩ := opLe_new h hbo hta htb hag hal hnew
    exact ⟨r1, by rw [r2]; simp⟩
  rw [pureL.mergeSort_append_of_lt (opLe_trans l) (opLe_total l) hanti hperm hord]
  exact List.prefix_append _ _

end Perennial.gryff.pure
