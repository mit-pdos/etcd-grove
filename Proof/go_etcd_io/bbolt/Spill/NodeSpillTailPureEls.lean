/-
`node.spill` after its children's loop (U9u, `notes/bbolt-proof-plan.md`; pure): **the leaf
elements of a written page** (`treeEls`): a written leaf page's are its inodes', a written branch
page's (over its children's `sTree`s) its children's in order.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Spill.TreeElsFuel

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section els
variable [GooseExts]

/-- An inode's leaf element by data. -/
def mEl (m : InodeM) : El := (m.flags.toNat, m.key, m.value)

theorem flatMap_range_getElem {α β : Type} (l : List α) (f : α → List β) :
    (List.range l.length).flatMap (fun i => ((l[i]?).map f).getD []) = l.flatMap f := by
  have : (List.range l.length).map (fun i => ((l[i]?).map f).getD []) = l.map f := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp [List.getElem?_eq_getElem h1]
  rw [List.flatMap_def, this, ← List.flatMap_def]

/-- **A written leaf page's leaf elements** are its inodes'. -/
theorem treeEls_wLeaf {P : Pages} {x : Nat} {wid : w64} {ms : List InodeM} {ovf : w32}
    {tail : List w8} (hpg : P !! x = some (wPage wid true ms ovf tail)) (hn : ms.length < 2 ^ 16)
    (hb : 16 + (pageBody true ms).length < 2 ^ 32) :
    treeEls P x = ms.map mEl := by
  have hc := wPage_count (id := wid) (leaf := true) (ovf := ovf) (tail := tail) hn
  have hfl : pageFlags (wPage wid true ms ovf tail) = leafPageFlag := by
    rw [wPage_flags]; rfl
  unfold treeEls treeLeaves
  rw [show P.size + 1 = P.size + 1 from rfl]
  simp only [leavesF, hpg, hfl, ite_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hc]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    obtain ⟨-, -, -, hf, hk, hv⟩ := wPage_leaf (id := wid) (ovf := ovf) (tail := tail) h1 hb
    simp [hf, hk, hv, mEl]

/-- **A written branch page's leaf elements** (its children `sTree`s of the pages `Sc i`, not
holding it) are its children's, in order. -/
theorem treeEls_wBranch {P : Pages} {hwm : Nat} {wid : w64} {ms : List InodeM} {ovf : w32}
    {tail : List w8} (hpg : P !! wid.toNat = some (wPage wid false ms ovf tail))
    (hn : ms.length < 2 ^ 16) (hb : 16 + (pageBody true ms).length < 2 ^ 32)
    (Sc : Nat → List Nat) (lc hc' : Nat → Option (List w8)) (hc : Nat → Nat)
    (hch : ∀ i (hix : i < ms.length), sTree P hwm ms[i].pgid.toNat (lc i) (hc' i) (hc i) (Sc i))
    (hown : ∀ i < ms.length, wid.toNat ∉ Sc i) :
    treeEls P wid.toNat = ms.flatMap fun m => treeEls P m.pgid.toNat := by
  have hcnt := wPage_count (id := wid) (leaf := false) (ovf := ovf) (tail := tail) hn
  have hfl : pageFlags (wPage wid false ms ovf tail) ≠ leafPageFlag := by
    rw [wPage_flags]; decide
  have hsub : ∀ i (hix : i < ms.length),
      leavesF P.size P ms[i].pgid.toNat = leavesF (P.size + 1) P ms[i].pgid.toNat := by
    intro i hix
    have hs := hch i hix
    have hroot : treeHas P ms[i].pgid.toNat ms[i].pgid.toNat := by
      cases hs.wf with | page _ pg _ _ hpg' => exact treeHas.root _ pg hpg'
    have hmu : muS P (Sc i) ms[i].pgid.toNat ≤ (Sc i).length := by
      unfold muS; exact List.length_filter_le _ _
    have hnd : (wid.toNat :: Sc i).Nodup := List.nodup_cons.2 ⟨hown i hix, hs.nodup⟩
    have hle := length_le_size (P := P) hnd (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · simp [hpg]
      · exact treeHas_isSome ((hs.has y).2 hy))
    simp only [List.length_cons] at hle
    exact leavesF_agree hs (fun _ _ => rfl) _ _ _ hroot hs.wf (by omega) (by omega)
  unfold treeEls treeLeaves
  conv => lhs; simp only [leavesF, hpg, hfl, ite_false]
  rw [hcnt, List.flatMap_assoc, ← flatMap_range_getElem ms]
  apply flatMap_congr_mem
  intro i hi
  have hi' := List.mem_range.1 hi
  have hbp := (wPage_branch (id := wid) (ovf := ovf) (tail := tail) hi' hb).2.2.1
  rw [List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some, hbp, hsub i hi']

end els

end Spill

end bbolt
end EtcdGrove
end Perennial
