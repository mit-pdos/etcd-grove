/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): pure laws for the budget laws
(`Within/<Act>.lean`): how much the binding's set, function-on-terms and configuration operations
can grow a value, and the budget of a list updated at one position.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Parts
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ActionLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

/-! ## The budget is monotone (`StateLaws.lean`'s laws, stated here without its section's
Goose instances, which pure laws do not use) -/

theorem logWithin.mono' {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {l : List Entry}
    (h : logWithin b E l) : logWithin b' E' l :=
  ⟨Nat.le_trans h.1 hb, fun e he => ⟨(h.2 e he).1, Nat.le_trans (h.2 e he).2 hE⟩⟩

theorem confWithin.mono' {V b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {c : Conf}
    (h : confWithin V b E c) : confWithin V b' E' c := by
  have hm : b * E ≤ b' * E' := Nat.mul_le_mul hb hE
  exact ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem termIntsWithin.mono' {b b' : Nat} (hb : b ≤ b') {f : TermFn Int}
    (h : termIntsWithin b f) : termIntsWithin b' f :=
  ⟨Nat.le_trans h.1 hb, h.2⟩

theorem Msg.Within.mono' {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {m : Msg}
    (h : m.Within b E) : m.Within b' E' :=
  ⟨h.1, Nat.le_trans h.2.1 hb, fun l hl e he => Nat.le_trans (h.2.2 l hl e he) hE⟩

theorem Event.Within.mono' {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {ev : Event}
    (h : ev.Within b E) : ev.Within b' E' :=
  ⟨h.1, Nat.le_trans h.2.1 hb, fun l hl e he => Nat.le_trans (h.2.2 l hl e he) hE⟩

theorem Pre.Within.mono' {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {u : Pre}
    (h : u.Within b E) : u.Within b' E' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8.mono' hb hE, by omega, by omega, h11, by omega, h13,
    by omega, h15⟩

/-- A state within a budget is within any larger one (`Ready` passes `OnDisk` the budget after the
report, `b + ev.weight`). -/
theorem State.Within.mono' {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {s : State}
    (h : s.Within b E) : s.Within b' E' := by
  obtain ⟨hc, hi1, hi2, h1, h2, h3, h4, h5, h6, hlog, hch, hll1, hll2, hcf, hlc1, hlc2, hla, hel,
    htl, hm1, hm2, hv1, hv2, hl1, hl2, hu, hp, hq, hr, hvi⟩ := h
  refine ⟨hc, hi1, by omega, h1, h2, h3, h4, h5, h6, fun l hl => (hlog l hl).mono' hb hE,
    hch.mono' hb hE, by omega, fun p hp => ⟨(hll2 p hp).1, (hll2 p hp).2.mono' hb hE⟩,
    fun c hc => (hcf c hc).mono' hb hE, by omega,
    fun p hp => ⟨(hlc2 p hp).1, (hlc2 p hp).2.mono' hb hE⟩, hla.mono' hb, hel.mono' hb, htl.mono' hb,
    by omega, hm2, by omega, hv2, by omega, hl2, fun o ho u hou => (hu o ho u hou).mono' hb hE,
    fun ms hms => ⟨by have := (hp ms hms).1; omega, fun m hm => ((hp ms hms).2 m hm).mono' hb hE⟩,
    fun q hq' => ⟨by have := (hq q hq').1; omega, fun it hit =>
      ⟨((hq q hq').2 it hit).1.mono' hb hE, by have := ((hq q hq').2 it hit).2.1; omega,
        fun m hm => (((hq q hq').2 it hit).2.2 m hm).mono' hb hE⟩⟩,
    fun r hr' => ⟨by have := (hr r hr').1; omega, (hr r hr').2⟩, by omega⟩


theorem setAdd_length_le (s : SSet) (x : Str) : (setAdd s x).length ≤ s.length + 1 := by
  unfold setAdd
  dsimp only
  split
  · omega
  · simp; omega

theorem setAdd_ne_nil (s : SSet) (x : Str) : setAdd s x ≠ [] := by
  unfold setAdd
  dsimp only
  split
  · rename_i h; intro hs; subst hs; simp at h
  · simp

theorem foldl_setAdd_length_le (t s : List Str) : (t.foldl setAdd s).length ≤ s.length + t.length := by
  induction t generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (setAdd s x); have := setAdd_length_le s x; omega

theorem setOf_length_le (xs : List Str) : (setOf xs).length ≤ xs.length := by
  unfold setOf; have := foldl_setAdd_length_le xs []; simpa using this

theorem SSet.union_length_le (s t : SSet) : (s.union t).length ≤ s.length + t.length := by
  unfold SSet.union; exact foldl_setAdd_length_le t s

theorem SSet.minus_length_le (s t : SSet) : (s.minus t).length ≤ s.length := by
  unfold SSet.minus; exact List.length_filter_le _ _

/-- `NextConf(c, d)`'s sets: at most `c`'s and `d`'s additions. -/
theorem nextConf_length {c c' : Conf} {d : Value} (h : nextConf c d = .ok c') :
    c'.cin.length ≤ c.cin.length + d.add.length ∧ c'.cout.length ≤ c.cin.length := by
  unfold nextConf at h
  obtain ⟨r, hr, h⟩ := bind_ok h
  unfold Value.asRec at hr
  split at hr
  · cases hr
  cases hr
  split at h
  · cases h; simp
  obtain ⟨t, ht, h⟩ := bind_ok h
  have htl : t.length ≤ c.cin.length + d.add.length := by
    unfold target at ht
    obtain ⟨r', hr', ht⟩ := bind_ok ht
    unfold Value.asRec at hr'
    split at hr'
    · cases hr'
    cases hr'; cases ht
    have h1 := SSet.minus_length_le (c.cin.union (setOf d.add)) (setOf d.remove)
    have h2 := SSet.union_length_le c.cin (setOf d.add)
    have h3 := setOf_length_le d.add
    omega
  split at h
  · cases h; exact ⟨htl, Nat.le_refl _⟩
  · cases h; simp; omega

theorem TermFn.with_length_le {α : Type} (f : TermFn α) (t : Int) (v : α) : (f.with t v).length ≤ f.length + 1 := by
  induction f with
  | nil => simp [TermFn.with]
  | cons p ps ih =>
    simp only [TermFn.with]
    split
    · split <;> simp
    · simp; omega

theorem TermFn.mem_with {α : Type} {f : TermFn α} {t : Int} {v : α} {q : Int × α} (h : q ∈ f.with t v) :
    q = (t, v) ∨ q ∈ f := by
  induction f with
  | nil => simp [TermFn.with] at h; exact .inl h
  | cons p ps ih =>
    simp only [TermFn.with] at h
    split at h
    · simp at h
      rcases h with h | h
      · exact .inl h
      · split at h
        · exact .inr (List.mem_cons_of_mem _ h)
        · exact .inr h
    · simp at h
      rcases h with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · rcases ih h with h' | h'; exact .inl h'; exact .inr (List.mem_cons_of_mem _ h')

theorem termIntsWithin_with {b : Nat} {f : TermFn Int} {t v : Int} (h : termIntsWithin b f) (ht : bigOk t)
    (hv : bigOk v) : termIntsWithin (b + 1) (f.with t v) := by
  refine ⟨by have := TermFn.with_length_le f t v; have := h.1; omega, fun q hq => ?_⟩
  rcases TermFn.mem_with hq with h' | h'
  · subst h'; exact ⟨ht, hv⟩
  · exact h.2 q h'

/-- A list within a per-element budget, one element replaced by one within it. -/
theorem forall_mem_set {α : Type} {P : α → Prop} {l : List α} {n : Nat} {x : α} (hl : ∀ y ∈ l, P y) (hx : P x) :
    ∀ y ∈ l.set n x, P y := fun y hy => by
  rcases mem_set_or hy with h | h
  · subst h; exact hx
  · exact hl y h

theorem bigOk_of_numOk {x : Int} (h : numOk x) : bigOk x := by
  unfold numOk numBound at h; unfold bigOk; omega

theorem getElem!_some_mem {α : Type} {l : List (Option α)} {n : Nat} {u : α} (h : l[n]! = some u) :
    some u ∈ l := by
  by_cases hn : n < l.length
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hn] at h
    simp at h; rw [← h]; exact List.getElem_mem hn
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h; cases h

theorem getElem!_mem' {α : Type} [Inhabited α] {P : α → Prop} {l : List α} {n : Nat} (hl : ∀ y ∈ l, P y)
    (hd : P default) : P l[n]! := by
  by_cases hn : n < l.length
  · exact hl _ (getElem!_mem hn)
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact hd

/-- `filterM` keeps some of the list's elements. -/
theorem filterM_sub {α : Type} {xs ys : List α} {f : α → EvalM Bool} (h : filterM xs f = .ok ys) :
    ys.length ≤ xs.length ∧ ∀ y ∈ ys, y ∈ xs := by
  unfold filterM at h
  suffices H : ∀ (l : List α) (acc ys : List α),
      l.foldlM (fun out x => do if (← f x) then pure (out ++ [x]) else pure out) acc = .ok ys →
      ys.length ≤ acc.length + l.length ∧ ∀ y ∈ ys, y ∈ acc ∨ y ∈ l by
    obtain ⟨h1, h2⟩ := H xs [] ys h
    exact ⟨by simpa using h1, fun y hy => by simpa using h2 y hy⟩
  intro l
  induction l with
  | nil => intro acc ys h; cases h; exact ⟨by simp, fun y hy => .inl hy⟩
  | cons x t ih =>
    intro acc ys h
    rw [List.foldlM_cons] at h
    obtain ⟨acc', hacc', h⟩ := bind_ok h
    obtain ⟨c, -, hacc'⟩ := bind_ok hacc'
    have hacc : acc'.length ≤ acc.length + 1 ∧ ∀ y ∈ acc', y ∈ acc ∨ y = x := by
      split at hacc'
      · cases hacc'; refine ⟨by simp, fun y hy => ?_⟩
        rcases List.mem_append.1 hy with hy | hy
        · exact .inl hy
        · exact .inr (List.mem_singleton.1 hy)
      · cases hacc'; exact ⟨by omega, fun y hy => .inl hy⟩
    obtain ⟨h1, h2⟩ := ih acc' ys h
    refine ⟨by simp; omega, fun y hy => ?_⟩
    rcases h2 y hy with hy' | hy'
    · rcases hacc.2 y hy' with hy'' | hy''
      · exact .inl hy''
      · exact .inr (hy'' ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ hy')

end AntCheck
end EtcdGrove
end Perennial
