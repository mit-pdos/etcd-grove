/-
The keys during rebalance (`RebalanceDefs.lean`), pure: the order of keys, bounds inside bounds
(`bndIn`), a tree's keys within looser bounds (`treeKeys_mono`), and the exact keys of
`txShape` with `brFirst` and `leafPg0` as the rebalance's keys (`rblKeysB_of`).
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceDefs
public import Proof.go_etcd_io.bbolt.WriteLeaf
public import Proof.go_etcd_io.bbolt.KeyOrder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-! ### The order of keys -/

theorem rk_lt_of_le_lt {a b c : List w8} (h1 : ¬ go.GoStringLt b a) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  rcases goStringLt_trichot a b with h | h | h
  · exact goStringLt_trans h h2
  · subst h; exact h2
  · exact absurd h h1

theorem rk_lt_of_lt_le {a b c : List w8} (h1 : go.GoStringLt a b) (h2 : ¬ go.GoStringLt c b) :
    go.GoStringLt a c := by
  rcases goStringLt_trichot b c with h | h | h
  · exact goStringLt_trans h1 h
  · subst h; exact h1
  · exact absurd h h2

theorem rk_le_trans {a b c : List w8} (h1 : ¬ go.GoStringLt b a) (h2 : ¬ go.GoStringLt c b) :
    ¬ go.GoStringLt c a := by
  intro h
  rcases goStringLt_trichot b c with h3 | h3 | h3
  · exact h1 (goStringLt_trans h3 h)
  · subst h3; exact h1 h
  · exact h2 h3

theorem rk_le_of_lt {a b : List w8} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a := by
  intro h'
  exact goStringLt_irrefl_w a (goStringLt_trans h h')

theorem rk_le_refl (a : List w8) : ¬ go.GoStringLt a a := goStringLt_irrefl_w a

/-! ### Bounds -/

theorem bndIn_refl (a : Option (List w8) × Option (List w8)) : bndIn a a :=
  ⟨fun y h => ⟨y, h, rk_le_refl y⟩, fun y h => ⟨y, h, rk_le_refl y⟩⟩

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

theorem bndIn_entry {a b : Option (List w8) × Option (List w8)} (h : bndIn a b) (ws : List WEntry)
    (i : Nat) : bndIn (entryBnd a ws i) (entryBnd b ws i) := by
  unfold entryBnd
  exact bndIn_child (lo := a.1) (hi := a.2) h _ _ _

/-- A tree's keys are within looser bounds. -/
theorem treeKeys_mono (pages : GMap Nat (List w8)) :
    ∀ c lo hi, treeKeys pages c lo hi → ∀ lo' hi', bndIn (lo, hi) (lo', hi') →
      treeKeys pages c lo' hi' := by
  intro c lo hi h
  induction h with
  | leaf root pg lo hi hpg hl hk hb =>
    intro lo' hi' hin
    exact treeKeys.leaf root pg lo' hi' hpg hl (fun i hi => keyIn_bndIn hin _ (hk i hi)) hb
  | branch root pg lo hi kind hpg hb h2 hk hc hs ih =>
    intro lo' hi' hin
    exact treeKeys.branch root pg lo' hi' kind hpg hb h2 (fun i hi => keyIn_bndIn hin _ (hk i hi)) hc
      (fun i hi => ih i hi _ _ (bndIn_child hin _ _ _))

/-! ### From the exact keys -/

theorem rblKeysB_of (W : WView) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : bktKeysB W B bnd) (hf : brFirst B bnd) (hp : leafPg0 B) : rblKeysB W B bnd none := by
  obtain ⟨h1, h2, h3⟩ := hk
  refine ⟨h1, h2, fun l r hr => ?_⟩
  obtain ⟨c1, -, c3, c4, c5, c6⟩ := h3 l r hr
  refine ⟨c1, fun hp' => ?_, fun hb => ?_, fun _ => c5, fun hl w hw => ⟨hp l r hr hl w hw, c6 hl w hw⟩⟩
  · obtain ⟨hkey, rp, i, w, hrp, hw, hpg, hwk, hb⟩ := c3 hp'
    exact ⟨hkey, rp, i, w, hrp, hw, hpg, hwk, by rw [hb]; exact bndIn_refl _⟩
  · obtain ⟨h2', kind, hkind⟩ := c4 hb
    exact ⟨fun _ => h2', hf l r hr hb, kind, hkind⟩

/-- The rebalance's keys, with no deficient node, are its keys with one. -/
theorem rblNodeKeys_dfc (W : WView) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) (l : Loc) (r : NRec) (h : rblNodeKeys W B bnd none l r) :
    rblNodeKeys W B bnd dfc l r := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨c1, c2, fun hb => ?_, fun _ => c4 (by simp), c5⟩
  obtain ⟨d1, d2, d3⟩ := c3 hb
  exact ⟨fun _ => d1 (by simp), d2, d3⟩

end pure

end bbolt
end EtcdGrove
end Perennial
