/-
The pure meaning of the interval tree's two coverage queries, over the model's in-order list
(`Model.lean`, `Tree.lean`): `Intersects` of a key's point interval is membership in some entry
(`stab_point_iff`), and `Contains(q)`, the greedy scan of the stabbed entries in tree order
(`containsRes`, the code's loop transcribed), is the coverage of every key of `q` by the entries
(`containsRes_iff`). The auth store's permission cache rests on both (the auth plan's S2,
2026-10-23; `notes/decisions.md`, "S2 of the auth plan"). Lean-first (no Rocq counterpart).

The point interval's lemmas (`strLt_succ_le`, `succ_ne_empty`, `ivlCmp_point_iff`) are the
watchable store's (`mvcc/InvWatchGroup.lean`), restated here so that `auth` does not import
`mvcc`; the successor lemma is a fact about `GoStringLt` that belongs in Perennial
(`notes/perennial-changes.md`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Tree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

section pure
variable [GooseExts]

/-! ## The affine order, non-strictly -/

theorem affLt_of_le_of_lt {a b c : GoString} (h1 : ¬ affLt b a) (h2 : affLt b c) : affLt a c := by
  rcases affLt_trichotomy a b with hab | rfl | hba
  · exact affLt_trans hab h2
  · exact h2
  · exact absurd hba h1

theorem affCmp_nonpos_iff (a b : GoString) : affCmp a b ≤ 0 ↔ ¬ affLt b a := by
  rw [← affCmp_pos_iff]; omega

/-! ## Membership in an interval -/

/-- The key `k` is in the affine interval `x = [b, e)`: not below `b`, below `e` (so `k ≠ ""`,
the top; `"" ` as `e` is open to the end of the key space). -/
def inIvl (x : IvlS) (k : GoString) : Prop := ¬ affLt k x.1 ∧ affLt k x.2

/-- An entry holding a key of the query overlaps it. -/
theorem ivlCmp_eq_zero_of_inIvl {q x : IvlS} {k : GoString} (hq : inIvl q k) (hx : inIvl x k) :
    ivlCmp q x = 0 := by
  rw [ivlCmp_eq_zero_iff]
  obtain ⟨hq1, hq2⟩ := hq
  obtain ⟨hx1, hx2⟩ := hx
  exact ⟨fun _ => affLt_of_le_of_lt hx1 hq2, affLt_of_le_of_lt hq1 hx2⟩

theorem mem_stab (q : IvlS) (L : List Entry) (z : Entry) :
    z ∈ stab q L ↔ z ∈ L ∧ ivlCmp q z.1 = 0 := by
  unfold stab; rw [List.mem_filter, decide_eq_true_iff]

/-- The stabbed entries, in the tree's order, are sorted by begin. -/
theorem stab_sorted_begin (q : IvlS) (L : List Entry) (hs : IvSorted L) :
    (stab q L).Pairwise fun a b => ¬ affLt b.1.1 a.1.1 := by
  unfold stab
  refine List.Pairwise.filter _ (hs.imp ?_)
  intro a b h hlt
  exact h ((ivlLt_iff _ _).2 (Or.inl hlt))

/-! ## The point interval of a key -/

/-- `k ++ "\x00"` is the immediate successor of `k`: a string above `k` is at least it. -/
theorem strLt_succ_le {k b : GoString} (h : go.GoStringLt k b) :
    k ++ go!"\x00" = b ∨ go.GoStringLt (k ++ go!"\x00") b := by
  induction k generalizing b with
  | nil =>
    cases h with
    | nil =>
      rename_i c bs
      by_cases hc : c = W8 0
      · subst hc
        cases bs with
        | nil => exact Or.inl rfl
        | cons d ds => exact Or.inr (List.Lex.cons List.Lex.nil)
      · right
        show List.Lex _ [W8 0] (c :: bs)
        apply List.Lex.rel
        have : uint.Z c ≠ 0 := by
          intro h0; apply hc; apply BitVec.eq_of_toNat_eq
          simp only [uint.Z] at h0; simp; omega
        have h1 : 0 ≤ uint.Z c := by simp [uint.Z]
        have h2 : uint.Z (W8 0) = 0 := by decide
        omega
  | cons x xs ih =>
    cases h with
    | cons h =>
      rcases ih h with e | h'
      · exact Or.inl (by rw [List.cons_append, e])
      · exact Or.inr (List.Lex.cons h')
    | rel h => exact Or.inr (List.Lex.rel h)

theorem succ_ne_empty (k : GoString) : k ++ go!"\x00" ≠ go!"" := by
  intro h; have := congrArg List.length h; simp at this

/-- The point interval of a key overlaps `[b, e)` exactly when the key is in it. -/
theorem ivlCmp_point_iff (k b e : GoString) :
    ivlCmp (k, k ++ go!"\x00") (b, e) = 0 ↔ affCmp k b ≥ 0 ∧ affCmp k e < 0 := by
  have hb := affCmp_bounds k b
  have he := affCmp_bounds k e
  have hsucc : affCmp k b < 0 → affCmp (k ++ go!"\x00") b ≤ 0 := by
    intro hkb
    obtain ⟨hk, hb'⟩ := (affCmp_neg_iff k b).1 hkb
    rcases hb' with rfl | hlt
    · have := (affCmp_neg_iff (k ++ go!"\x00") go!"").2 ⟨succ_ne_empty k, Or.inl rfl⟩
      omega
    · rcases strLt_succ_le hlt with heq | hlt'
      · rw [heq, affCmp_self]; omega
      · have hbne : b ≠ go!"" := by
          rintro rfl; cases hlt
        have := (affCmp_neg_iff (k ++ go!"\x00") b).2 ⟨succ_ne_empty k, Or.inr hlt'⟩
        omega
  unfold ivlCmp
  simp only
  split
  · rename_i h; have := h.1; omega
  · rename_i h
    have h1 : ¬ affCmp k b < 0 := fun h1 => h ⟨h1, hsucc h1⟩
    split <;> omega

/-- **`Intersects` of a key's point interval**: some entry holds the key. -/
theorem stab_point_iff (k : GoString) (L : List Entry) :
    stab (k, k ++ go!"\x00") L ≠ [] ↔ ∃ z ∈ L, inIvl z.1 k := by
  constructor
  · intro hne
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne
    rw [mem_stab] at hz
    refine ⟨z, hz.1, ?_⟩
    have := (ivlCmp_point_iff k z.1.1 z.1.2).1 hz.2
    exact ⟨(affCmp_nonneg_iff _ _).1 this.1, (affCmp_neg_iff _ _).1 this.2⟩
  · rintro ⟨z, hz, h1, h2⟩
    refine List.ne_nil_of_mem ((mem_stab _ _ _).2 ⟨hz, ?_⟩)
    exact (ivlCmp_point_iff k z.1.1 z.1.2).2
      ⟨(affCmp_nonneg_iff _ _).2 h1, (affCmp_neg_iff _ _).2 h2⟩

/-! ## `Contains` -/

/-- `Contains`' scan from the running maximum end `me` over the remaining stabbed entries (in
tree order): `none` when the loop breaks (an entry begins above the running maximum, a gap),
else the final maximum (an entry's end replaces it when above it). -/
def scanFrom (me : GoString) : List Entry → Option GoString
  | [] => some me
  | z :: zs => if affCmp me z.1.1 < 0 then none
      else scanFrom (if affCmp z.1.2 me > 0 then z.1.2 else me) zs

/-- **What `Contains(q)` returns**: no stabbed entry, `false`; else the scan from the first's end
over the rest must not break, and the final maximum is at or above `q`'s end while the first's
begin (the least, in tree order) is at or below `q`'s begin. -/
def containsRes (q : IvlS) (L : List Entry) : Bool :=
  match stab q L with
  | [] => false
  | z :: zs =>
    match scanFrom z.1.2 zs with
    | none => false
    | some me => decide (affCmp me q.2 ≥ 0 ∧ affCmp z.1.1 q.1 ≤ 0)

/-- The scan over one more entry: it breaks when the entry begins above the running maximum,
else the maximum takes the entry's end when above it (`Contains`' loop body). -/
theorem scanFrom_snoc (z : Entry) : ∀ (zs : List Entry) (me : GoString),
    scanFrom me (zs ++ [z]) = match scanFrom me zs with
      | none => none
      | some me' => if affCmp me' z.1.1 < 0 then none
          else some (if affCmp z.1.2 me' > 0 then z.1.2 else me')
  | [], me => by simp only [List.nil_append, scanFrom]
  | w :: ws, me => by
    simp only [List.cons_append, scanFrom]
    split
    · rfl
    · exact scanFrom_snoc z ws _

/-- A scan that broke stays broken over more entries. -/
theorem scanFrom_none_append (ws : List Entry) : ∀ (zs : List Entry) (me : GoString),
    scanFrom me zs = none → scanFrom me (zs ++ ws) = none
  | [], me, h => by simp [scanFrom] at h
  | w :: zs, me, h => by
    simp only [List.cons_append, scanFrom] at h ⊢
    split
    · rfl
    · rename_i hw
      rw [if_neg hw] at h
      exact scanFrom_none_append ws zs _ h

/-- A key below the scan's final maximum is below its initial one or in a scanned entry. -/
theorem scanFrom_cover (zs : List Entry) : ∀ (me me' : GoString), scanFrom me zs = some me' →
    ∀ k, affLt k me' → affLt k me ∨ ∃ z ∈ zs, inIvl z.1 k := by
  induction zs with
  | nil => intro me me' h k hk; simp only [scanFrom, Option.some.injEq] at h; subst h; exact Or.inl hk
  | cons z zs ih =>
    intro me me' h k hk
    simp only [scanFrom] at h
    split at h
    · cases h
    rename_i hgap
    rw [affCmp_neg_iff] at hgap
    rcases ih _ _ h k hk with h1 | ⟨w, hw, hwk⟩
    · split at h1
      · rename_i hup
        by_cases hkme : affLt k me
        · exact Or.inl hkme
        · right
          refine ⟨z, List.mem_cons_self, ?_, h1⟩
          intro hkb
          exact hkme (affLt_of_lt_of_le hkb hgap)
      · exact Or.inl h1
    · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hwk⟩

/-- The scan's final maximum is at or above its initial one and every scanned entry's end. -/
theorem scanFrom_max (zs : List Entry) : ∀ (me me' : GoString), scanFrom me zs = some me' →
    ¬ affLt me' me ∧ ∀ z ∈ zs, ¬ affLt me' z.1.2 := by
  induction zs with
  | nil =>
    intro me me' h; simp only [scanFrom, Option.some.injEq] at h; subst h
    exact ⟨affLt_irrefl _, by simp⟩
  | cons z zs ih =>
    intro me me' h
    simp only [scanFrom] at h
    split at h
    · cases h
    obtain ⟨h1, h2⟩ := ih _ _ h
    split at h1
    · rename_i hup
      rw [affCmp_pos_iff] at hup
      refine ⟨affLe_trans (affLt_asymm hup) h1, ?_⟩
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact h1
      · exact h2 w hw
    · rename_i hup
      rw [affCmp_pos_iff] at hup
      refine ⟨h1, ?_⟩
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact affLe_trans hup h1
      · exact h2 w hw

/-- A broken scan: a prefix scanned to a maximum below the begin of the next entry. -/
theorem scanFrom_none (zs : List Entry) : ∀ (me : GoString), scanFrom me zs = none →
    ∃ (P : List Entry) (z : Entry) (S : List Entry) (me0 : GoString),
      zs = P ++ z :: S ∧ scanFrom me P = some me0 ∧ affLt me0 z.1.1 := by
  induction zs with
  | nil => intro me h; simp [scanFrom] at h
  | cons z zs ih =>
    intro me h
    simp only [scanFrom] at h
    split at h
    · rename_i hgap
      exact ⟨[], z, zs, me, rfl, rfl, (affCmp_neg_iff _ _).1 hgap⟩
    · rename_i hgap
      obtain ⟨P, w, S, me0, hzs, hP, hlt⟩ := ih _ h
      refine ⟨z :: P, w, S, me0, by rw [hzs]; rfl, ?_, hlt⟩
      simp only [scanFrom, hgap, ↓reduceIte]
      exact hP

/-- **`Contains(q)` is the coverage of `q`**: for a query `[b, e)` with `b` below `e` (so `b` not
the top `""`) over entries in the tree's order, the scan succeeds exactly when every key of the
query is in some entry. -/
theorem containsRes_iff (q : IvlS) (L : List Entry) (hs : IvSorted L) (hq : affLt q.1 q.2) :
    containsRes q L = true ↔ ∀ k, inIvl q k → ∃ z ∈ L, inIvl z.1 k := by
  have hsub : ∀ z ∈ stab q L, z ∈ L := fun z hz => ((mem_stab _ _ _).1 hz).1
  have hov : ∀ z ∈ stab q L, ivlCmp q z.1 = 0 := fun z hz => ((mem_stab _ _ _).1 hz).2
  have hsorted := stab_sorted_begin q L hs
  -- coverage by the entries is coverage by the stabbed entries
  have hcov : (∀ k, inIvl q k → ∃ z ∈ L, inIvl z.1 k) ↔
      ∀ k, inIvl q k → ∃ z ∈ stab q L, inIvl z.1 k := by
    constructor
    · intro H k hk
      obtain ⟨z, hz, hzk⟩ := H k hk
      exact ⟨z, (mem_stab _ _ _).2 ⟨hz, ivlCmp_eq_zero_of_inIvl hk hzk⟩, hzk⟩
    · intro H k hk
      obtain ⟨z, hz, hzk⟩ := H k hk
      exact ⟨z, hsub z hz, hzk⟩
  rw [hcov]
  unfold containsRes
  rcases hS : stab q L with _ | ⟨z0, zs⟩ <;> dsimp only
  · -- no stabbed entry: `q`'s begin is uncovered
    simp only [Bool.false_eq_true, false_iff]
    intro H
    obtain ⟨z, hz, -⟩ := H q.1 ⟨affLt_irrefl _, hq⟩
    cases hz
  rw [hS] at hsub hov hsorted
  have hz0 := hov z0 List.mem_cons_self
  rw [ivlCmp_eq_zero_iff] at hz0
  rw [List.pairwise_cons] at hsorted
  rcases hsc : scanFrom z0.1.2 zs with _ | me <;> dsimp only
  · -- the scan broke at `z`, after a prefix `P` scanned to `me0`: `me0` is a key of `q` no entry
    -- holds (the prefix ends at or below it, the rest begins above it)
    simp only [Bool.false_eq_true, false_iff]
    intro H
    obtain ⟨P, z, S, me0, hzs, hP, hgap⟩ := scanFrom_none zs _ hsc
    obtain ⟨hme0, hPmax⟩ := scanFrom_max P _ _ hP
    have hz := hov z (by rw [hzs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
    rw [ivlCmp_eq_zero_iff] at hz
    have hq1me0 : affLt q.1 me0 := affLt_of_lt_of_le hz0.2 hme0
    have hzb : affLt z.1.1 q.2 := hz.1 (affLt_trans hq1me0 hgap)
    obtain ⟨w, hw, hw1, hw2⟩ := H me0 ⟨affLt_asymm hq1me0, affLt_trans hgap hzb⟩
    rw [hzs] at hw hsorted
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hme0 hw2
    rcases List.mem_append.1 hw with hw | hw
    · exact hPmax w hw hw2
    · -- `w` is `z` or after it: it begins at or above `z`
      have hwz : ¬ affLt w.1.1 z.1.1 := by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact affLt_irrefl _
        · have := List.pairwise_append.1 hsorted.2
          exact (List.pairwise_cons.1 this.2.1).1 w hw
      exact hw1 (affLt_of_lt_of_le hgap hwz)
  · -- the scan reached `me`: `[z0.begin, me)` is the union of the stabbed entries
    obtain ⟨hme, hmax⟩ := scanFrom_max zs _ _ hsc
    rw [decide_eq_true_iff, affCmp_nonneg_iff, affCmp_nonpos_iff]
    constructor
    · rintro ⟨h1, h2⟩ k ⟨hk1, hk2⟩
      have hkme : affLt k me := affLt_of_lt_of_le hk2 h1
      rcases scanFrom_cover zs _ _ hsc k hkme with h | ⟨w, hw, hwk⟩
      · exact ⟨z0, List.mem_cons_self, affLe_trans h2 hk1, h⟩
      · exact ⟨w, List.mem_cons_of_mem _ hw, hwk⟩
    · intro H
      constructor
      · -- `me` below `q`'s end would be an uncovered key of `q`
        intro hc
        have hq1me : affLt q.1 me := affLt_of_lt_of_le hz0.2 hme
        obtain ⟨w, hw, -, hw2⟩ := H me ⟨affLt_asymm hq1me, hc⟩
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hme hw2
        · exact hmax w hw hw2
      · -- `q`'s begin is in some stabbed entry, which begins at or above `z0`
        obtain ⟨w, hw, hw1, -⟩ := H q.1 ⟨affLt_irrefl _, hq⟩
        have hwz0 : ¬ affLt w.1.1 z0.1.1 := by
          rcases List.mem_cons.1 hw with rfl | hw
          · exact affLt_irrefl _
          · exact hsorted.1 w hw
        exact affLe_trans hwz0 hw1

end pure

end adt
end EtcdGrove
end Perennial
