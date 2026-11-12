/-
The start of `node.rebalance`: the node is no longer marked unbalanced (`rblStart`, the bucket
`B0`), and the cases where it then returns, the node being big enough or a root (`rbl_done`).
Ported from `old/bbolt/.../RebalanceStart.lean` (pure part).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblFrame

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rbl
variable [GooseExts]

/-- The node `r` no longer marked unbalanced. -/
def rblClear (r : NRec) : NRec := { r with nv := { r.nv with unbalanced' := false } }

/-- The bucket with the node `nl` no longer marked unbalanced. -/
def rblStart (B : BRec) (nl : Loc) (r : NRec) : BRec := { B with ns := <[nl := rblClear r]> B.ns }

theorem nrecEq_clear (r : NRec) : nrecEq r (rblClear r) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (v : View) (hwm : Nat) (bl : Loc)

theorem rbl_dfc_ne (dfc : Option Loc) (nl y : Loc) (h : dfc = none ∨ dfc = some nl) (hy : y ≠ nl) :
    dfc ≠ some y := by
  rcases h with rfl | rfl
  · nofun
  · intro e; cases e; exact hy rfl

/-- At the start: the node is the deficient one. -/
theorem rblB_start (B : BRec) (nl : Loc) (r : NRec) (dfc : Option Loc)
    (hB : rblB v hwm bl B dfc) (hr : B.ns !! nl = some r) (hd : dfc = none ∨ dfc = some nl) :
    rblB v hwm bl (rblStart B nl r) (some nl) := by
  have hs := bktSim_set B nl r (rblClear r) hr (nrecEq_clear r)
  obtain ⟨hc, ⟨bnd, hk⟩, ha, hh⟩ := hB
  refine ⟨bktClean_sim v hwm bl hs hc, ⟨bnd, rblKeysB_sim v hs bnd dfc (some nl) hk ?_ ?_⟩,
    rblAcyc_sim hs ha, rblHt_sim v hs hh⟩
  · intro y ry hy hl hne
    have hyn : y ≠ nl := by intro e; exact hne (by rw [e])
    exact ((hk.2.2 y ry hy).2.2.1 hl).1 (rbl_dfc_ne dfc nl y hd hyn)
  · intro y ry' hy hne
    have hyn : y ≠ nl := by intro e; exact hne (by rw [e])
    change (<[nl := rblClear r]> B.ns) !! y = some ry' at hy
    rw [rf_lookup, if_neg hyn] at hy
    exact (hk.2.2 y ry' hy).2.2.2.1 (rbl_dfc_ne dfc nl y hd hyn)

/-- The node, no longer marked unbalanced, is big enough: no deficient node. -/
theorem rbl_done (B : BRec) (nl : Loc) (r : NRec) (dfc : Option Loc)
    (hB : rblB v hwm bl B dfc) (hr : B.ns !! nl = some r) (hd : dfc = none ∨ dfc = some nl)
    (h2 : r.nv.isLeaf' = false → 2 ≤ r.ws.length)
    (h1 : r.nv.isLeaf' = true → r.nv.parent' ≠ null → 0 < r.ws.length) :
    rblB v hwm bl (rblStart B nl r) none ∧ rblStep B (rblStart B nl r) nl ∧
      ∀ k bv, entryIn v B k bv → entryIn v (rblStart B nl r) k bv := by
  have hs := bktSim_set B nl r (rblClear r) hr (nrecEq_clear r)
  obtain ⟨hc, ⟨bnd, hk⟩, ha, hh⟩ := hB
  refine ⟨⟨bktClean_sim v hwm bl hs hc, ⟨bnd, rblKeysB_sim v hs bnd dfc none hk ?_ ?_⟩,
      rblAcyc_sim hs ha, rblHt_sim v hs hh⟩,
    ⟨rfl, rfl, rfl, fun y ry' hy hu => ?_⟩, fun k bv he => entryIn_sim v hs k bv he⟩
  · intro y ry hy hl _
    by_cases hyn : y = nl
    · subst hyn; rw [hr] at hy; cases hy; exact h2 hl
    · exact ((hk.2.2 y ry hy).2.2.1 hl).1 (rbl_dfc_ne dfc nl y hd hyn)
  · intro y ry' hy _
    change (<[nl := rblClear r]> B.ns) !! y = some ry' at hy
    rw [rf_lookup] at hy
    by_cases hyn : y = nl
    · rw [if_pos hyn] at hy; cases hy
      intro hl _ hp; exact h1 hl hp
    · rw [if_neg hyn] at hy
      exact (hk.2.2 y ry' hy).2.2.2.1 (rbl_dfc_ne dfc nl y hd hyn)
  · change (<[nl := rblClear r]> B.ns) !! y = some ry' at hy
    rw [rf_lookup] at hy
    by_cases hyn : y = nl
    · rw [if_pos hyn] at hy; cases hy; simp [rblClear] at hu
    · rw [if_neg hyn] at hy
      exact ⟨hyn, ry', hy, hu, rfl⟩

end rbl

end bbolt
end EtcdGrove
end Perennial
