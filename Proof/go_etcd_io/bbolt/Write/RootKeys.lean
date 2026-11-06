/-
Item 5 (`notes/bbolt-proof-plan.md`, item 3/batch 43.4): the keys of the view pages under a page
position of the root bucket are at most `MaxKeySize` (`Write/MatOK.newNodeBnd`'s `hroot`): a
leaf's by `posShape`'s name clause, a branch's by exact branch keys (`treeKeys`: element `i`'s key
is its child's first key), by induction on `treeKeys`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Wtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open go_etcd_io.bbolt

section rootkeys
variable [GooseExts]

/-- `ownHas` extended by one branch step at its end. -/
theorem ownHas_snoc (pages : Pages) (c p : Nat) (h : ownHas pages c p) (pg : List w8)
    (hp : pages !! p = some pg) (hb : pageFlags pg = branchPageFlag) (i : Nat)
    (hi : i < pageCount pg) (cpg : List w8) (hc : pages !! branchPgid pg i = some cpg) :
    ownHas pages c (branchPgid pg i) := by
  induction h with
  | root root pg0 h0 => exact ownHas.child root pg i _ hp hb hi (ownHas.root _ cpg hc)
  | child root pg0 i0 id h0 hb0 hi0 _ ih => exact ownHas.child root pg0 i0 _ h0 hb0 hi0 (ih hp)

/-- **The keys of the pages under `c`, at most `MaxKeySize`**, given its leaves' (`hleaf`) and the
B+tree keys from a page `p` under `c`. -/
theorem pageKeys_le_of_treeKeys (pages : Pages) (c : Nat)
    (hleaf : ∀ p pg, ownHas pages c p → pages !! p = some pg → pageFlags pg = leafPageFlag →
      ∀ j < pageCount pg, leafKsize pg j ≤ maxKeySize)
    (p : Nat) (lo hi : Option (List w8)) (hk : treeKeys pages p lo hi) :
    ownHas pages c p → ∀ pg, pages !! p = some pg →
    ∀ j < pageCount pg, (pageKey pg j).length ≤ maxKeySize := by
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
    exact ih j hj (ownHas_snoc pages c root ho pg hp hf j hj cpg hc) cpg hc 0 hcnt

/-- `posShape`'s name clause as `pageKeys_le_of_treeKeys`' `hleaf`, for the root bucket. -/
theorem posShape_rootLeaf (X : WX) (hps : posShape X) (B : BRec) (hB : X.t.bs !! X.rl = some B)
    (c : Nat) (hc : posRoot B c) :
    ∀ p pg, ownHas X.v.pages c p → X.v.pages !! p = some pg → pageFlags pg = leafPageFlag →
      ∀ j < pageCount pg, leafKsize pg j ≤ maxKeySize :=
  fun p pg ho hp hf j hj => (hps X.rl B hB c p pg hc ho hp hf j hj).2.2.1 rfl

end rootkeys

end Write

end bbolt
end EtcdGrove
end Perennial
