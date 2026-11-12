/-
`node.spill` (U9w3, `notes/bbolt-proof-plan.md`; pure): **the children's parent pointers**
(`parOK`, `Spill/UTree`) through a node's record set keeping its parent and adding no children
(`parOK_setNode`, the sort's permutation `parOK_perm`), the kill of `n`'s children
(`parOK_nilCh`); and what the kill needs of them (`parOK_uniq`: no other live node has `n`'s
children). The frames, the split and the pieces' loop: `Spill/ParOK`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesKill
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesStep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section par
variable [GooseExts]

/-- **A node's record set** keeping its parent and adding no children. -/
theorem parOK_setNode {X : WX} {bl n : Loc} {r : NRec} (h : parOK X bl)
    (hn : X.node bl n = some r) (r' : NRec) (hpar : r'.nv.parent' = r.nv.parent')
    (hcs : ∀ c ∈ r'.cs, c ∈ r.cs) : parOK (X.setNode bl n r') bl := by
  have hnode : ∀ l, (X.setNode bl n r').node bl l = if l = n then some r' else X.node bl l := by
    intro l
    by_cases e : l = n
    · subst e; rw [if_pos rfl]; exact WX.setNode_node_same hn r'
    · rw [if_neg e]; exact WX.setNode_node_ne bl r' e
  -- a child's node after, pointing to `m` if it did before
  have hch : ∀ m c rc, X.node bl c = some rc → rc.nv.parent' = m →
      ∃ rc', (X.setNode bl n r').node bl c = some rc' ∧ rc'.nv.parent' = m := by
    intro m c rc hc hp
    by_cases e : c = n
    · subst e; rw [hn] at hc; cases hc
      exact ⟨r', by rw [hnode, if_pos rfl], by rw [hpar, hp]⟩
    · exact ⟨rc, by rw [hnode, if_neg e]; exact hc, hp⟩
  intro m rm' hm' hlv'
  rw [WX.setNode_live] at hlv'
  rw [hnode] at hm'
  intro c hc
  by_cases e : m = n
  · subst e; rw [if_pos rfl] at hm'; cases hm'
    obtain ⟨rc, hrc, hp⟩ := h m r hn hlv' c (hcs c hc)
    exact hch m c rc hrc hp
  · rw [if_neg e] at hm'
    obtain ⟨rc, hrc, hp⟩ := h m rm' hm' hlv' c hc
    exact hch m c rc hrc hp

/-- **The sort of `n`'s children** (a permutation). -/
theorem parOK_perm {X : WX} {bl n : Loc} {rn : NRec} {l : List Loc} (h : parOK X bl)
    (hn : X.node bl n = some rn) (hp : rn.cs.Perm l) :
    parOK (X.setNode bl n { rn with cs := l }) bl :=
  parOK_setNode h hn _ rfl fun c hc => hp.symm.subset hc

/-- Fewer live nodes. -/
theorem parOK_killL {X : WX} {bl : Loc} (h : parOK X bl) (L : List Loc) :
    parOK (X.killL L) bl := by
  intro m rm hm hlv c hc
  change X.node bl m = some rm at hm
  rw [killL_live] at hlv
  obtain ⟨rc, hrc, hp⟩ := h m rm hm hlv.1 c hc
  exact ⟨rc, hrc, hp⟩

/-- **`n.children = nil`**. -/
theorem parOK_nilCh {X : WX} {bl n : Loc} {r : NRec} (h : parOK X bl)
    (hn : X.node bl n = some r) : parOK (X.nilCh bl n r) bl :=
  parOK_killL (parOK_setNode h hn r.nilCh rfl (fun c hc => by simp [NRec.nilCh] at hc)) r.cs

/-- **What the kill of `n`'s children needs**: each is a node of `bl` whose parent is `n` (not
`null`), and no other live node has one of them as a child. -/
theorem parOK_uniq {X : WX} {bl n : Loc} {r : NRec} (h : parOK X bl)
    (hn : X.node bl n = some r) (hlv : n ∈ X.live) :
    (∀ c ∈ r.cs, ∃ rc, X.node bl c = some rc ∧ rc.nv.parent' = n) ∧
    (∀ m rm, X.node bl m = some rm → m ∈ X.live → m ≠ n → ∀ c ∈ rm.cs, c ∉ r.cs) := by
  refine ⟨h n r hn hlv, fun m rm hm hmlv hne c hc hcn => hne ?_⟩
  obtain ⟨rc, hrc, hp⟩ := h m rm hm hmlv c hc
  obtain ⟨rc', hrc', hp'⟩ := h n r hn hlv c hcn
  rw [hrc] at hrc'; cases hrc'
  rw [← hp, hp']

end par

end Spill

end bbolt
end EtcdGrove
end Perennial
