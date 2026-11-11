/-
The keys during rebalance (`RblDefs.lean`), pure: the order of keys, bounds inside bounds
(`bndIn`), a tree's keys within looser bounds (`treeKeys_mono`), the exact keys with `brFirst`
and `leafPg0` as the rebalance's keys (`rblKeysB_of`), and back: the rebalance's keys with
acyclic parents give exact keys (`bktKeys_of_rbl`), the exact bounds defined top-down along the
parent chain (`exactBnd`). Ported from `old/bbolt/.../RebalanceKeys.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rbl
variable [GooseExts]

/-! ### The order of keys -/

theorem rk_lt_of_le_lt {a b c : List w8} (h1 : ¬ go.GoStringLt b a) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  by_cases hab : go.GoStringLt a b
  · exact go.goStringLt_trans hab h2
  · have e := go.goStringLt_eq_of_not_lt hab h1
    subst e; exact h2

theorem rk_lt_of_lt_le {a b c : List w8} (h1 : go.GoStringLt a b) (h2 : ¬ go.GoStringLt c b) :
    go.GoStringLt a c := by
  by_cases hbc : go.GoStringLt b c
  · exact go.goStringLt_trans h1 hbc
  · have e := go.goStringLt_eq_of_not_lt hbc h2
    subst e; exact h1

theorem rk_le_trans {a b c : List w8} (h1 : ¬ go.GoStringLt b a) (h2 : ¬ go.GoStringLt c b) :
    ¬ go.GoStringLt c a := by
  intro h
  exact h2 (rk_lt_of_lt_le h h1)

theorem rk_le_of_lt {a b : List w8} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a :=
  go.goStringLt_asymm h

theorem rk_le_refl (a : List w8) : ¬ go.GoStringLt a a := go.goStringLt_irrefl a

/-! ### Bounds -/

theorem bndIn_refl (a : Option (List w8) × Option (List w8)) : bndIn a a :=
  ⟨fun y h => ⟨y, h, rk_le_refl y⟩, fun y h => ⟨y, h, rk_le_refl y⟩⟩

/-- Every bound is inside no bound. -/
theorem bndIn_none (a : Option (List w8) × Option (List w8)) : bndIn a (none, none) :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem bndIn_trans {a b c : Option (List w8) × Option (List w8)} (h1 : bndIn a b)
    (h2 : bndIn b c) : bndIn a c := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := h2.1 z hz
    obtain ⟨x, hx, hxy⟩ := h1.1 y hy
    exact ⟨x, hx, rk_le_trans hyz hxy⟩
  · obtain ⟨y, hy, hyz⟩ := h2.2 z hz
    obtain ⟨x, hx, hxy⟩ := h1.2 y hy
    exact ⟨x, hx, rk_le_trans hxy hyz⟩

theorem keyIn_bndIn {a b : Option (List w8) × Option (List w8)} (h : bndIn a b) (k : List w8)
    (hk : keyIn a.1 a.2 k) : keyIn b.1 b.2 k := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxy⟩ := h.1 y hy
    exact rk_le_trans hxy (hk.1 x hx)
  · obtain ⟨x, hx, hxy⟩ := h.2 y hy
    exact rk_lt_of_lt_le (hk.2 x hx) hxy

/-- A lower bound below `a`'s, the same upper bound. -/
theorem bndIn_lo {a : Option (List w8) × Option (List w8)} (lo : Option (List w8))
    (h : ∀ y, lo = some y → ∃ x, a.1 = some x ∧ ¬ go.GoStringLt x y) : bndIn a (lo, a.2) :=
  ⟨h, fun y hy => ⟨y, hy, rk_le_refl y⟩⟩

/-- An upper bound above `a`'s, the same lower bound. -/
theorem bndIn_hi {a : Option (List w8) × Option (List w8)} (hi : Option (List w8))
    (h : ∀ y, hi = some y → ∃ x, a.2 = some x ∧ ¬ go.GoStringLt y x) : bndIn a (a.1, hi) :=
  ⟨fun y hy => ⟨y, hy, rk_le_refl y⟩, h⟩

theorem bndIn_child {lo hi lo' hi' : Option (List w8)} (h : bndIn (lo, hi) (lo', hi'))
    (ks : Nat → List w8) (n i : Nat) :
    bndIn (childLo lo ks i, childHi hi ks n i) (childLo lo' ks i, childHi hi' ks n i) := by
  unfold childLo childHi
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · simp only at hy ⊢
    by_cases hi0 : i = 0
    · rw [if_pos hi0] at hy ⊢; exact h.1 y hy
    · rw [if_neg hi0] at hy ⊢; exact ⟨y, hy, rk_le_refl y⟩
  · simp only at hy ⊢
    by_cases hin : i + 1 < n
    · rw [if_pos hin] at hy ⊢; exact ⟨y, hy, rk_le_refl y⟩
    · rw [if_neg hin] at hy ⊢; exact h.2 y hy

theorem bndIn_entry {a b : Option (List w8) × Option (List w8)} (h : bndIn a b)
    (ks : List (List w8)) (i : Nat) : bndIn (entryBnd a ks i) (entryBnd b ks i) := by
  unfold entryBnd
  exact bndIn_child (lo := a.1) (hi := a.2) h _ _ _

theorem bndIn_wEntry {a b : Option (List w8) × Option (List w8)} (h : bndIn a b)
    (ws : List WEntry) (i : Nat) : bndIn (wEntryBnd a ws i) (wEntryBnd b ws i) :=
  bndIn_entry h _ i

/-- A tree's keys are within looser bounds. -/
theorem treeKeys_mono (pages : Pages) :
    ∀ c lo hi, treeKeys pages c lo hi → ∀ lo' hi', bndIn (lo, hi) (lo', hi') →
      treeKeys pages c lo' hi' := by
  intro c lo hi h
  induction h with
  | leaf root pg lo hi hpg hl hk hb =>
    intro lo' hi' hin
    exact treeKeys.leaf root pg lo' hi' hpg hl (fun i hi => keyIn_bndIn hin _ (hk i hi)) hb
  | branch root pg lo hi kind hpg hb h2 hk hc hs ih =>
    intro lo' hi' hin
    exact treeKeys.branch root pg lo' hi' kind hpg hb h2
      (fun i hi => keyIn_bndIn hin _ (hk i hi)) hc
      (fun i hi => ih i hi _ _ (bndIn_child hin _ _ _))

/-! ### From the exact keys -/

theorem rblKeysB_of (v : View) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : bktKeysB v B bnd) (hf : brFirst B bnd) (hp : leafPg0 B) : rblKeysB v B bnd none := by
  obtain ⟨h1, h2, h3⟩ := hk
  refine ⟨h1, h2, fun l r hr => ?_⟩
  obtain ⟨c1, -, c3, c4, c5, c6⟩ := h3 l r hr
  refine ⟨c1, fun hp' => ?_, fun hb => ?_, fun _ => c5,
    fun hl w hw => ⟨hp l r hr hl w hw, c6 hl w hw⟩⟩
  · obtain ⟨hkey, rp, i, w, hrp, hw, hpg, hwk, hb⟩ := c3 hp'
    exact ⟨hkey, rp, i, w, hrp, hw, hpg, hwk, by rw [hb]; exact bndIn_refl _⟩
  · obtain ⟨h2', kind, hkind⟩ := c4 hb
    exact ⟨fun _ => h2', hf l r hr hb, kind, hkind⟩

/-- The rebalance's keys, with no deficient node, are its keys with one. -/
theorem rblNodeKeys_dfc (v : View) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) (l : Loc) (r : NRec) (h : rblNodeKeys v B bnd none l r) :
    rblNodeKeys v B bnd dfc l r := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨c1, c2, fun hb => ?_, fun _ => c4 (by simp), c5⟩
  obtain ⟨d1, d2, d3⟩ := c3 hb
  exact ⟨fun _ => d1 (by simp), d2, d3⟩

/-! ### Back to the exact keys -/

/-- The exact bounds of the nodes of `B`, top-down along the parent chain: a root's are none, a
node's are its parent's entry's (`idx l`, of the parent's entries) under its parent's. The
recursion is on the acyclicity height `ht` (a parent's is above its child's, at most `M`). -/
def exactBnd (B : BRec) (ht : Loc → Nat) (M : Nat) (idx : Loc → Nat) (l : Loc) :
    Option (List w8) × Option (List w8) :=
  match B.ns !! l with
  | none => (none, none)
  | some r =>
    if r.nv.parent' = null then (none, none) else
    if _h1 : ht l < ht r.nv.parent' then
      if _h2 : ht r.nv.parent' ≤ M then
        match B.ns !! r.nv.parent' with
        | some rp => wEntryBnd (exactBnd B ht M idx r.nv.parent') rp.ws (idx l)
        | none => (none, none)
      else (none, none)
    else (none, none)
termination_by M - ht l
decreasing_by omega

theorem exactBnd_root (B : BRec) (ht : Loc → Nat) (M : Nat) (idx : Loc → Nat) (l : Loc)
    (r : NRec) (hl : B.ns !! l = some r) (hp : r.nv.parent' = null) :
    exactBnd B ht M idx l = (none, none) := by
  rw [exactBnd]; simp only [hl, hp, if_true]

theorem exactBnd_child (B : BRec) (ht : Loc → Nat) (M : Nat) (idx : Loc → Nat) (l : Loc)
    (r rp : NRec) (hl : B.ns !! l = some r) (hp : r.nv.parent' ≠ null)
    (hrp : B.ns !! r.nv.parent' = some rp) (h1 : ht l < ht r.nv.parent')
    (h2 : ht r.nv.parent' ≤ M) :
    exactBnd B ht M idx l = wEntryBnd (exactBnd B ht M idx r.nv.parent') rp.ws (idx l) := by
  rw [exactBnd]; simp only [hl, hp, if_false, dif_pos h1, dif_pos h2, hrp]

/-- A choice of an index for every `a` that has one. -/
theorem idx_choice {α : Type} (P : α → Nat → Prop) : ∃ f : α → Nat, ∀ a, (∃ i, P a i) → P a (f a) := by
  classical
  exact ⟨fun a => if hx : ∃ i, P a i then Classical.choose hx else 0,
    fun a ha => by simp only [dif_pos ha]; exact Classical.choose_spec ha⟩

/-- A bound on a function over the keys of a finite map. -/
theorem gmap_bound {V : Type} (m : GMap Loc V) (f : Loc → Nat) :
    ∃ M, ∀ l x, m !! l = some x → f l ≤ M := by
  have hL : ∀ L : List (Loc × V), ∃ M, ∀ p ∈ L, f p.1 ≤ M := by
    intro L
    induction L with
    | nil => exact ⟨0, fun _ h => nomatch h⟩
    | cons a L ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨max (f a.1) M, fun p hp => ?_⟩
      rcases List.mem_cons.1 hp with e | hp
      · subst e; omega
      · have := hM p hp; omega
  obtain ⟨M, hM⟩ := hL m.toList
  exact ⟨M, fun l x hx => hM (l, x) ((GMap.mem_toList m l x).2 hx)⟩

/-- **Rebalance's keys give the exact keys.** With no deficient node and acyclic parents, the
exact bounds (`exactBnd`, the widest consistent with the structure) contain the rebalance's
bounds, so the nodes' keys, and their unmaterialized children's trees, are within them. -/
theorem bktKeys_of_rbl (v : View) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (h : rblKeysB v B bnd none) (ha : rblAcyc B) : bktKeys v B := by
  obtain ⟨ht, hht⟩ := ha
  obtain ⟨M, hM⟩ := gmap_bound B.ns ht
  obtain ⟨idx, hidx⟩ := idx_choice (fun l i => ∀ r, B.ns !! l = some r → r.nv.parent' ≠ null →
    ∃ rp w, B.ns !! r.nv.parent' = some rp ∧ rp.ws[i]? = some w ∧ w.pgid = r.nv.pgid' ∧
      w.key = r.key ∧ bndIn (bnd l) (wEntryBnd (bnd r.nv.parent') rp.ws i))
  have hix : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null →
      ∃ rp w, B.ns !! r.nv.parent' = some rp ∧ rp.ws[idx l]? = some w ∧ w.pgid = r.nv.pgid' ∧
        w.key = r.key ∧ bndIn (bnd l) (wEntryBnd (bnd r.nv.parent') rp.ws (idx l)) := by
    intro l r hl hp
    refine hidx l ?_ r hl hp
    obtain ⟨-, rp, i, w, hrp, hw, hwp, hwk, hb⟩ := (h.2.2 l r hl).2.1 hp
    exact ⟨i, fun r' hr' _ => by
      rw [hl] at hr'; cases hr'; exact ⟨rp, w, hrp, hw, hwp, hwk, hb⟩⟩
  have hin : ∀ n l r, M - ht l ≤ n → B.ns !! l = some r →
      bndIn (bnd l) (exactBnd B ht M idx l) := by
    intro n
    induction n with
    | zero =>
      intro l r hn hl
      by_cases hp : r.nv.parent' = null
      · rw [exactBnd_root B ht M idx l r hl hp]; exact bndIn_none _
      · obtain ⟨rp, -, hrp, -⟩ := hix l r hl hp
        have := hht l r hl hp; have := hM _ rp hrp; omega
    | succ n ih =>
      intro l r hn hl
      by_cases hp : r.nv.parent' = null
      · rw [exactBnd_root B ht M idx l r hl hp]; exact bndIn_none _
      · obtain ⟨rp, w, hrp, -, -, -, hb⟩ := hix l r hl hp
        have h1 := hht l r hl hp; have h2 := hM _ rp hrp
        rw [exactBnd_child B ht M idx l r rp hl hp hrp h1 h2]
        exact bndIn_trans hb (bndIn_wEntry (ih _ rp (by omega) hrp) rp.ws (idx l))
  have hin' : ∀ l r, B.ns !! l = some r → bndIn (bnd l) (exactBnd B ht M idx l) :=
    fun l r hl => hin _ l r (Nat.le_refl _) hl
  refine ⟨exactBnd B ht M idx, h.1, h.2.1, fun l r hl => ?_⟩
  obtain ⟨n1, n2, n3, n4, n5⟩ := h.2.2 l r hl
  refine ⟨fun w hw => keyIn_bndIn (hin' l r hl) _ (n1 w hw),
    fun hp => exactBnd_root B ht M idx l r hl hp, fun hp => ?_, fun hb => ?_,
    fun hlf hu hp => n4 (by simp) hlf hu hp, fun hlf w hw => (n5 hlf w hw).2⟩
  · obtain ⟨rp, w, hrp, hw, hwp, hwk, -⟩ := hix l r hl hp
    exact ⟨(n2 hp).1, rp, idx l, w, hrp, hw, hwp, hwk,
      exactBnd_child B ht M idx l r rp hl hp hrp (hht l r hl hp) (hM _ rp hrp)⟩
  · obtain ⟨d1, -, kind, d3⟩ := n3 hb
    refine ⟨d1 (by simp), kind, fun i w hw => ⟨(d3 i w hw).1, fun hn => ?_⟩⟩
    obtain ⟨pg, a1, a2, a3, a4, a5⟩ := (d3 i w hw).2 hn
    exact ⟨pg, a1, a2, a3, a4,
      treeKeys_mono _ _ _ _ a5 _ _ (bndIn_wEntry (hin' l r hl) r.ws i)⟩

end rbl

end bbolt
end EtcdGrove
end Perennial
