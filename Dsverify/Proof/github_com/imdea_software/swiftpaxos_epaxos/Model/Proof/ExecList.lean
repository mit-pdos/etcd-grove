/-
List facts for the execution proofs (p-modelexec): `before l a b` (`a` occurs before `b` in `l`),
and the slots lists (`Sys.slotsOn`, `Sys.lexec`): membership, order, no duplicates.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace ExecOrd

/-! ## `before` -/

/-- `a` occurs before `b` in `l`. -/
def before {α : Type} (l : List α) (a b : α) : Prop := ∃ l1 l2, l = l1 ++ l2 ∧ a ∈ l1 ∧ b ∈ l2

theorem before_of_idx {α : Type} {l : List α} {p q : Nat} {a b : α} (hpq : p < q)
    (ha : l[p]? = some a) (hb : l[q]? = some b) : before l a b := by
  refine ⟨l.take (p + 1), l.drop (p + 1), (List.take_append_drop _ _).symm, ?_, ?_⟩
  · rw [List.mem_iff_getElem?]
    exact ⟨p, by rw [List.getElem?_take]; simp [ha]⟩
  · rw [List.mem_iff_getElem?]
    exact ⟨q - (p + 1), by rw [List.getElem?_drop, show p + 1 + (q - (p + 1)) = q by omega]; exact hb⟩

theorem before_mem {α : Type} {l : List α} {a b : α} (h : before l a b) : a ∈ l ∧ b ∈ l := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  exact ⟨List.mem_append_left _ h1, List.mem_append_right _ h2⟩

theorem before_append {α : Type} {l1 l2 : List α} {a b : α} (h1 : a ∈ l1) (h2 : b ∈ l2) :
    before (l1 ++ l2) a b := ⟨l1, l2, rfl, h1, h2⟩

theorem before_append_right {α : Type} {A B : List α} {a b : α} (h : before B a b) :
    before (A ++ B) a b := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  exact ⟨A ++ l1, l2, by simp, List.mem_append_right _ h1, h2⟩

theorem before_cons_iff {α : Type} {c : α} {t : List α} {a b : α} :
    before (c :: t) a b ↔ (a = c ∧ b ∈ t) ∨ before t a b := by
  constructor
  · rintro ⟨l1, l2, h, h1, h2⟩
    cases l1 with
    | nil => cases h1
    | cons d l1 =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases List.mem_cons.mp h1 with e | e
      · exact Or.inl ⟨e, List.mem_append_right _ h2⟩
      · exact Or.inr ⟨l1, l2, rfl, e, h2⟩
  · rintro (⟨rfl, h⟩ | ⟨l1, l2, rfl, h1, h2⟩)
    · exact ⟨[a], t, rfl, by simp, h⟩
    · exact ⟨c :: l1, l2, rfl, List.mem_cons_of_mem _ h1, h2⟩

theorem before_cons {α : Type} {c : α} {t : List α} {a b : α} (h : before t a b) :
    before (c :: t) a b := before_cons_iff.mpr (Or.inr h)

theorem before_or {α : Type} {l : List α} {a b : α} (hab : a ≠ b) (ha : a ∈ l) (hb : b ∈ l) :
    before l a b ∨ before l b a := by
  induction l with
  | nil => cases ha
  | cons c t ih =>
    rcases List.mem_cons.mp ha with ea | ea
    · rcases List.mem_cons.mp hb with eb | eb
      · exact absurd (ea.trans eb.symm) hab
      · exact Or.inl (before_cons_iff.mpr (Or.inl ⟨ea, eb⟩))
    · rcases List.mem_cons.mp hb with eb | eb
      · exact Or.inr (before_cons_iff.mpr (Or.inl ⟨eb, ea⟩))
      · rcases ih ea eb with h | h
        · exact Or.inl (before_cons h)
        · exact Or.inr (before_cons h)

theorem before_asymm {α : Type} {l : List α} (hn : l.Nodup) {a b : α} (h1 : before l a b)
    (h2 : before l b a) : False := by
  induction l with
  | nil => exact absurd (before_mem h1).1 (by simp)
  | cons c t ih =>
    have hc : c ∉ t := (List.nodup_cons.mp hn).1
    rcases before_cons_iff.mp h1 with ⟨e1, -⟩ | h1' <;>
    rcases before_cons_iff.mp h2 with ⟨e2, ha⟩ | h2'
    · subst e1; exact hc ha
    · subst e1; exact hc (before_mem h2').2
    · subst e2; exact hc (before_mem h1').2
    · exact ih (List.nodup_cons.mp hn).2 h1' h2'

theorem before_irrefl {α : Type} {l : List α} (hn : l.Nodup) {a : α} (h : before l a a) : False :=
  before_asymm hn h h

theorem before_sublist {α : Type} {l l' : List α} (hs : l.Sublist l') {a b : α}
    (h : before l a b) : before l' a b := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  obtain ⟨r1, r2, rfl, s1, s2⟩ := List.append_sublist_iff.mp hs
  exact ⟨r1, r2, rfl, s1.subset h1, s2.subset h2⟩

theorem before_pre {α : Type} {l pre post : List α} {e e' : α} (hn : l.Nodup)
    (hl : l = pre ++ e :: post) (h : before l e' e) : e' ∈ pre := by
  have hm := (before_mem h).1
  rw [hl] at hm
  rcases List.mem_append.mp hm with h1 | h1
  · exact h1
  · rcases List.mem_cons.mp h1 with h2 | h2
    · subst h2; exact absurd h (fun h => before_irrefl hn h)
    · exfalso
      refine before_asymm hn h ⟨pre ++ [e], post, by rw [hl]; simp, by simp, h2⟩

theorem before_pairwise {α : Type} {R : α → α → Prop} {l : List α} (hp : l.Pairwise R)
    {a b : α} (h : before l a b) : R a b := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  exact (List.pairwise_append.mp hp).2.2 a h1 b h2

theorem before_append_iff {α : Type} {A B : List α} {a b : α} (h : before (A ++ B) a b) :
    before A a b ∨ (a ∈ A ∧ b ∈ B) ∨ before B a b := by
  obtain ⟨l1, l2, he, h1, h2⟩ := h
  rcases List.append_eq_append_iff.mp he with ⟨xs1, h3, h4⟩ | ⟨bs, h3, h4⟩
  · -- `l1 = A ++ xs1`, `B = xs1 ++ l2`
    subst h3 h4
    rcases List.mem_append.mp h1 with h5 | h5
    · exact Or.inr (Or.inl ⟨h5, List.mem_append_right _ h2⟩)
    · exact Or.inr (Or.inr ⟨xs1, l2, rfl, h5, h2⟩)
  · -- `A = l1 ++ bs`, `l2 = bs ++ B`
    subst h3 h4
    rcases List.mem_append.mp h2 with h5 | h5
    · exact Or.inl ⟨l1, bs, rfl, h1, h5⟩
    · exact Or.inr (Or.inl ⟨List.mem_append_left _ h1, h5⟩)

/-- Order in a `flatMap` whose blocks are tagged by their source and internally ordered. -/
theorem before_flatMap {α β : Type} {R : β → β → Prop} (f : α → List β) (g : β → α)
    (hg : ∀ x, ∀ u ∈ f x, g u = x) (hp : ∀ x, (f x).Pairwise R) :
    ∀ (xs : List α) (u v : β), before (xs.flatMap f) u v →
      (g u = g v ∧ R u v) ∨ before xs (g u) (g v)
  | [], u, v, h => by simp at h; exact absurd (before_mem h).1 (by simp)
  | x :: xs, u, v, h => by
    rw [List.flatMap_cons] at h
    rcases before_append_iff h with h1 | ⟨h1, h2⟩ | h1
    · have e1 := hg x u (before_mem h1).1
      have e2 := hg x v (before_mem h1).2
      exact Or.inl ⟨e1.trans e2.symm, before_pairwise (hp x) h1⟩
    · right
      rw [hg x u h1]
      obtain ⟨y, hy, hv⟩ := List.mem_flatMap.mp h2
      rw [hg y v hv]
      exact before_cons_iff.mpr (Or.inl ⟨rfl, hy⟩)
    · rcases before_flatMap f g hg hp xs u v h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (before_cons h2)

/-- Two prefixes of a list without duplicates, with the same elements, are equal. -/
theorem prefix_eq_of_mem {α : Type} {a b L : List α} (ha : a <+: L) (hb : b <+: L) (hL : L.Nodup)
    (hab : ∀ z, z ∈ a ↔ z ∈ b) : a = b := by
  have key : ∀ {a b : List α}, a <+: b → b <+: L → (∀ z, z ∈ b → z ∈ a) → a = b := by
    intro a b h1 h2 h3
    obtain ⟨t, rfl⟩ := h1
    cases t with
    | nil => simp
    | cons z t =>
      exfalso
      have hn : (a ++ z :: t).Nodup := hL.sublist h2.sublist
      have hz := h3 z (by simp)
      exact (List.nodup_append.mp hn).2.2 z hz z (by simp) rfl
  rcases List.prefix_or_prefix_of_prefix ha hb with h | h
  · exact key h hb (fun z hz => (hab z).mpr hz)
  · exact (key h ha (fun z hz => (hab z).mp hz)).symm

/-! ## Slots -/

/-- The commands replica state `σ` holds for `x`. -/
def cmdsAt (σ : RState) (x : InstId) : List WCmd := ((σ.inst x).bind (·.cmds)).getD []

/-- Slot `e` is a non-NONE command touching key `k` of the command list `cs` (stage 2: was "on
key `k`"). -/
def slotAt (cs : List WCmd) (k : w64) (e : Slot × WCmd) : Prop :=
  e.1.2 < cs.length ∧ e.2 = cs.getD e.1.2 default ∧ e.2.op ≠ opNONE ∧ Sys.touches e.2 k

/-- The block of `slotsOn` for one instance. -/
def blk (σ : RState) (k : w64) (x : InstId) : List (Slot × WCmd) :=
  ((List.range (cmdsAt σ x).length).map (fun idx => ((x, idx), (cmdsAt σ x).getD idx default))).filter
    (fun e => e.2.op ≠ opNONE ∧ Sys.touches e.2 k)

theorem slotsOn_eq (σ : RState) (xs : List InstId) (k : w64) :
    Sys.slotsOn σ xs k = xs.flatMap (blk σ k) := rfl

theorem mem_blk (σ : RState) (k : w64) (x : InstId) (e : Slot × WCmd) :
    e ∈ blk σ k x ↔ e.1.1 = x ∧ slotAt (cmdsAt σ x) k e := by
  obtain ⟨⟨y, idx⟩, c⟩ := e
  simp only [blk, slotAt, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨j, hj, ⟨rfl, rfl⟩, rfl⟩, h1, h2⟩
    exact ⟨rfl, hj, rfl, h1, h2⟩
  · rintro ⟨rfl, hj, rfl, h1, h2⟩
    exact ⟨⟨idx, hj, ⟨rfl, rfl⟩, rfl⟩, h1, h2⟩

theorem blk_tag (σ : RState) (k : w64) (x : InstId) : ∀ u ∈ blk σ k x, u.1.1 = x :=
  fun u hu => ((mem_blk σ k x u).mp hu).1

theorem blk_pairwise (σ : RState) (k : w64) (x : InstId) :
    (blk σ k x).Pairwise (fun u v => u.1.2 < v.1.2) := by
  unfold blk
  refine List.Pairwise.sublist (List.filter_sublist) ?_
  rw [List.pairwise_map]
  exact List.pairwise_lt_range

theorem mem_slotsOn (σ : RState) (xs : List InstId) (k : w64) (e : Slot × WCmd) :
    e ∈ Sys.slotsOn σ xs k ↔ e.1.1 ∈ xs ∧ slotAt (cmdsAt σ e.1.1) k e := by
  rw [slotsOn_eq, List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨rfl, h⟩ := (mem_blk σ k x e).mp he
    exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨e.1.1, hx, (mem_blk σ k _ e).mpr ⟨rfl, h⟩⟩

theorem before_slotsOn (σ : RState) (xs : List InstId) (k : w64) (u v : Slot × WCmd)
    (h : before (Sys.slotsOn σ xs k) u v) :
    (u.1.1 = v.1.1 ∧ u.1.2 < v.1.2) ∨ before xs u.1.1 v.1.1 := by
  rw [slotsOn_eq] at h
  exact before_flatMap (blk σ k) (fun u => u.1.1) (blk_tag σ k) (blk_pairwise σ k) xs u v h

theorem slotsOn_nodup (σ : RState) (k : w64) :
    ∀ (xs : List InstId), xs.Nodup → (Sys.slotsOn σ xs k).Nodup
  | [], _ => by simp [Sys.slotsOn]
  | x :: xs, hn => by
    rw [slotsOn_eq, List.flatMap_cons, ← slotsOn_eq]
    rw [List.nodup_append]
    refine ⟨?_, slotsOn_nodup σ k xs (List.nodup_cons.mp hn).2, ?_⟩
    · refine List.Pairwise.imp ?_ (blk_pairwise σ k x)
      intro u v h e; rw [e] at h; exact Nat.lt_irrefl _ h
    · intro u hu v hv e
      subst e
      have h1 := blk_tag σ k x u hu
      have h2 := ((mem_slotsOn σ xs k u).mp hv).1
      rw [h1] at h2
      exact (List.nodup_cons.mp hn).1 h2

/-! ## The executed sequence of a replica -/

theorem lexec_sublist (S : Sys) (r : Nat) (k : w64) :
    (S.lexec r k).Sublist (Sys.slotsOn (S.rep r) (S.execLog r ++ (S.execCur r).take 1) k) := by
  unfold Sys.lexec Sys.curSlots
  cases S.execCur r with
  | nil => simp
  | cons x rest =>
    simp only [List.take_succ_cons, List.take_zero]
    rw [slotsOn_eq (S.rep r) (S.execLog r ++ [x]), List.flatMap_append]
    exact List.Sublist.append_left (List.filter_sublist) _

theorem mem_lexec (S : Sys) (r : Nat) (k : w64) (e : Slot × WCmd) :
    e ∈ S.lexec r k ↔ slotAt (cmdsAt (S.rep r) e.1.1) k e ∧
      (e.1.1 ∈ S.execLog r ∨ ((S.execCur r).head? = some e.1.1 ∧ e.1.2 < S.execIdx r)) := by
  unfold Sys.lexec Sys.curSlots
  rw [List.mem_append, mem_slotsOn]
  cases hc : S.execCur r with
  | nil => simp [and_comm]
  | cons x rest =>
    simp only [List.mem_filter, mem_slotsOn, List.mem_singleton, List.head?_cons, Option.some.injEq,
      decide_eq_true_eq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨h2, Or.inl h1⟩
      · exact ⟨h2, Or.inr ⟨h1.symm, h3⟩⟩
    · rintro ⟨h1, h2 | ⟨h2, h3⟩⟩
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨⟨h2.symm, h1⟩, h3⟩

/-! ## The component order (copied from `Epaxos/Proof/epaxos/ExecModel.lean`, which imports the
model's laws and so cannot be imported here) -/

/-- `nodeArray.Less` on ids: `(Seq, replica, instance)`, strictly, lexicographically. -/
def keyLt (σ : RState) (a b : InstId) : Prop :=
  let sa := ((σ.inst a).map (·.seq)).getD 0
  let sb := ((σ.inst b).map (·.seq)).getD 0
  zz sa < zz sb ∨ (sa = sb ∧ (a.q < b.q ∨ (a.q = b.q ∧ a.i < b.i)))

theorem zz_inj {a b : w32} (h : zz a = zz b) : a = b := by
  simp only [zz, sint.Z] at h; exact BitVec.toInt_inj.mp h

theorem sccLe_iff (σ : RState) (a b : InstId) : sccLe σ a b = true ↔ ¬ keyLt σ b a := by
  unfold sccLe keyLt
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  generalize ((σ.inst a).map (·.seq)).getD 0 = sa
  generalize ((σ.inst b).map (·.seq)).getD 0 = sb
  have hslt : sa.slt sb = true ↔ zz sa < zz sb := by simp [BitVec.slt, zz, sint.Z]
  rw [hslt]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · rintro (h' | ⟨e, -⟩)
      · omega
      · rw [e] at h; omega
    · rintro (h' | ⟨-, h'⟩)
      · omega
      · omega
  · intro h
    by_cases h1 : zz sa < zz sb
    · exact Or.inl h1
    · right
      have h2 : zz sa = zz sb := by
        exact Classical.byContradiction fun hne => h (Or.inl (by omega))
      have e := zz_inj h2
      refine ⟨e, ?_⟩
      refine Classical.byContradiction fun hh => ?_
      exact h (Or.inr ⟨e.symm, by omega⟩)

theorem sccLe_trans (σ : RState) (a b c : InstId) (h1 : sccLe σ a b = true)
    (h2 : sccLe σ b c = true) : sccLe σ a c = true := by
  rw [sccLe_iff] at *
  unfold keyLt at *
  intro h
  generalize ((σ.inst a).map (·.seq)).getD 0 = sa at *
  generalize ((σ.inst b).map (·.seq)).getD 0 = sb at *
  generalize ((σ.inst c).map (·.seq)).getD 0 = sc at *
  rcases h with h | ⟨e, h⟩
  · by_cases hb : zz sb < zz sa
    · exact h1 (Or.inl hb)
    · by_cases hb' : zz sc < zz sb
      · exact h2 (Or.inl hb')
      · omega
  · by_cases hb : zz sb < zz sa
    · exact h1 (Or.inl hb)
    · by_cases hb' : zz sa < zz sb
      · exact h2 (Or.inl (by rw [e]; exact hb'))
      · have e2 := zz_inj (show zz sb = zz sa by omega)
        have hh1 : ¬ (b.q < a.q ∨ (b.q = a.q ∧ b.i < a.i)) := fun hh => h1 (Or.inr ⟨e2, hh⟩)
        have hh2 : ¬ (c.q < b.q ∨ (c.q = b.q ∧ c.i < b.i)) :=
          fun hh => h2 (Or.inr ⟨by rw [e, e2], hh⟩)
        omega

theorem sccLe_total (σ : RState) (a b : InstId) : (sccLe σ a b || sccLe σ b a) = true := by
  rw [Bool.or_eq_true, sccLe_iff, sccLe_iff]
  refine Classical.byContradiction fun h => ?_
  simp only [not_or, Classical.not_not] at h
  obtain ⟨h1, h2⟩ := h
  unfold keyLt at h1 h2
  rcases h1 with h1 | ⟨e, h1⟩ <;> rcases h2 with h2 | ⟨e', h2⟩
  · omega
  · rw [e'] at h1; omega
  · rw [e] at h2; omega
  · omega

theorem sccLe_antisymm (σ : RState) (a b : InstId) (h1 : sccLe σ a b = true)
    (h2 : sccLe σ b a = true) : a = b := by
  rw [sccLe_iff] at h1 h2
  unfold keyLt at h1 h2
  generalize ((σ.inst a).map (·.seq)).getD 0 = sa at *
  generalize ((σ.inst b).map (·.seq)).getD 0 = sb at *
  have e := zz_inj (show zz sa = zz sb by
    refine Classical.byContradiction fun hne => ?_
    rcases Int.lt_or_gt_of_ne hne with h | h
    · exact h2 (Or.inl h)
    · exact h1 (Or.inl h))
  have hh1 : ¬ (b.q < a.q ∨ (b.q = a.q ∧ b.i < a.i)) := fun hh => h1 (Or.inr ⟨e.symm, hh⟩)
  have hh2 : ¬ (a.q < b.q ∨ (a.q = b.q ∧ a.i < b.i)) := fun hh => h2 (Or.inr ⟨e, hh⟩)
  obtain ⟨q1, i1⟩ := a; obtain ⟨q2, i2⟩ := b
  simp only [InstId.mk.injEq] at hh1 hh2 ⊢
  omega

end ExecOrd

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
