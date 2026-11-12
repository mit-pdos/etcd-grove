/-
`txClean`'s root shapes (`leafShape`, `posShape`) through a rebalance step (U8f,
`notes/bbolt-proof-plan.md`): a step changes one bucket's record, `B` to `B'`, keeping the view
and the root bucket's location; `B'`'s leaf entries are `B`'s (or of the root shape), and its page
positions are `B`'s (or under one of them): `shapes_frame`. Its callers are `rblX`'s producers
(`RblXSSim.rblX_sim`, `RblXSKill.rblX_kill`, `RblXSMat.rblX_mat`). `pageKeys_le_of_treeKeysN` is
`Write/RootKeys.pageKeys_le_of_treeKeys` for any bound (a materialized branch's keys within
`bboltEntryMax`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.RootKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt

section shape
variable [GooseExts]

/-- **The root shapes through a change of one bucket's record** (see the module doc). -/
theorem shapes_frame (X X' : WX) (bl : Loc) (B B' : BRec)
    (hv : X'.v = X.v) (hrl : X'.rl = X.rl) (hb : X.t.bs !! bl = some B)
    (hbs : ∀ c, X'.t.bs !! c = if c = bl then some B' else X.t.bs !! c)
    (hleaf : ∀ y ry', B'.ns !! y = some ry' → ry'.nv.isLeaf' = true → ∀ w ∈ ry'.ws,
      (isBktFlag w.flags ↔ bl = X.rl) ∨
        ∃ y2 ry2, B.ns !! y2 = some ry2 ∧ ry2.nv.isLeaf' = true ∧ w ∈ ry2.ws)
    (hpos : ∀ c p, posRoot B' c → ownHas X.v.pages c p →
      ∃ c0, posRoot B c0 ∧ ownHas X.v.pages c0 p)
    (hLS : leafShape X) (hPS : posShape X) : leafShape X' ∧ posShape X' := by
  constructor
  · intro c C hC y ry hy hl w hw
    rw [hrl]
    rw [hbs] at hC
    split at hC
    · rename_i hc; subst hc; cases hC
      rcases hleaf y ry hy hl w hw with h | ⟨y2, ry2, h2, hl2, hw2⟩
      · exact h
      · exact hLS c B hb y2 ry2 h2 hl2 w hw2
    · exact hLS c C hC y ry hy hl w hw
  · intro c C hC q p pg hq ho hp hf i hi
    rw [hrl]
    rw [hv] at ho hp ⊢
    rw [hbs] at hC
    split at hC
    · rename_i hc; subst hc; cases hC
      obtain ⟨c0, hc0, ho0⟩ := hpos q p hq ho
      exact hPS c B hb c0 p pg hc0 ho0 hp hf i hi
    · exact hPS c C hC q p pg hq ho hp hf i hi

/-- `hpos` from the positions' pages: `B'`'s page positions are `B`'s (same header). -/
theorem posRoot_of_pagePos {B B' : BRec} (hbv : B'.bv = B.bv) (hib : B'.ib = B.ib)
    (hpp : ∀ y j c, pagePosAt B' y j c → ∃ y' j', pagePosAt B y' j' c) (pages : Pages) :
    ∀ c p, posRoot B' c → ownHas pages c p → ∃ c0, posRoot B c0 ∧ ownHas pages c0 p := by
  intro c p hc ho
  refine ⟨c, ?_, ho⟩
  unfold posRoot at hc ⊢
  rw [hbv, hib] at hc
  rcases hc with h1 | ⟨y, j, hp, hlt⟩
  · exact Or.inl h1
  · obtain ⟨y', j', hp'⟩ := hpp y j _ hp
    exact Or.inr ⟨y', j', hp', hlt⟩

omit [GooseExts] in
theorem w64_natCast_inj (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have := congrArg BitVec.toNat h
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-- **The keys of the pages under `c`, at most `N`**, given its leaves' (`hleaf`) and the B+tree
keys from a page `p` under `c` (`Write.pageKeys_le_of_treeKeys` with any bound). -/
theorem pageKeys_le_of_treeKeysN (pages : Pages) (c N : Nat)
    (hleaf : ∀ p pg, ownHas pages c p → pages !! p = some pg → pageFlags pg = leafPageFlag →
      ∀ j < pageCount pg, leafKsize pg j ≤ N)
    (p : Nat) (lo hi : Option (List w8)) (hk : treeKeys pages p lo hi) :
    ownHas pages c p → ∀ pg, pages !! p = some pg →
    ∀ j < pageCount pg, (pageKey pg j).length ≤ N := by
  induction hk with
  | leaf root pg0 lo hi h0 hf _ _ =>
    intro ho pg hp j hj
    have e : pg = pg0 := Option.some.inj (hp.symm.trans h0); subst e
    have hl := hleaf root pg ho hp hf j hj
    have : pageKey pg j = leafKey pg j := by unfold pageKey; rw [ite_eq_left_iff.2 (fun h => absurd (by rw [hf]; rfl) h)]
    rw [this]; unfold leafKey bytesAt
    exact Nat.le_trans (List.length_take_le _ _) hl
  | branch root pg0 lo hi kind h0 hf _ _ hch _ ih =>
    intro ho pg hp j hj
    have e : pg = pg0 := Option.some.inj (hp.symm.trans h0); subst e
    have : pageKey pg j = branchKey pg j := by
      unfold pageKey; rw [ite_eq_right_iff.2 (fun h => absurd h (by rw [hf]; unfold branchPageFlag; decide))]
    rw [this]
    obtain ⟨cpg, hc, hcnt, -, hck⟩ := hch j hj
    rw [← hck]
    exact ih j hj (Write.ownHas_snoc pages c root ho pg hp hf j hj cpg hc) cpg hc 0 hcnt

end shape

end bbolt
end EtcdGrove
end Perennial
