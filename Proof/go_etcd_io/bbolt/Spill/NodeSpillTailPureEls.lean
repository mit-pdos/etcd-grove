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

/-- **A written leaf page is a finished subtree** from its first key: over its nested buckets'
values, its leaf elements its inodes'. -/
theorem fTree_wLeaf {P : Pages} {hwm : Nat} {hi : Option (List w8)}
    (wid : w64) (ms : List InodeM) (ovf : w32) (tail : List w8) (Sb : Nat → List Nat)
    (hpg : P !! wid.toNat = some (wPage wid true ms ovf tail)) (h2 : 2 ≤ wid.toNat)
    (hlen : (wPage wid true ms ovf tail).length = (1 + ovf.toNat) * 4096)
    (hn0 : 0 < ms.length) (hn : ms.length < 2 ^ 16)
    (hb : 16 + (pageBody true ms).length ≤ maxAllocSize) (hs : msSorted ms)
    (hk0 : ∀ m ∈ ms, 0 < m.key.length) (hkin : ∀ m ∈ ms, keyIn (some (msKey ms 0)) hi m.key)
    (hbv : ∀ i (hix : i < ms.length), ms[i].flags.toNat % 2 = bucketLeafFlag →
      bvalS P hwm ms[i].value (Sb i))
    (hb0 : ∀ i (hix : i < ms.length), ms[i].flags.toNat % 2 ≠ bucketLeafFlag → Sb i = [])
    (hd : subsDisj P wid.toNat (wPage wid true ms ovf tail) ms.length Sb)
    (hext : wid.toNat + (1 + ovf.toNat) ≤ hwm) :
    fTree P hwm wid.toNat (msKey ms 0) hi 0 (nodePages wid.toNat ms.length Sb) (ms.map mEl) := by
  have hb32 : 16 + (pageBody true ms).length < 2 ^ 32 := by unfold maxAllocSize at hb; omega
  refine ⟨sTree_wLeaf wid ms ovf tail Sb hpg h2 (by omega) hlen hn hb hs hk0 hkin hbv hb0 hd hext,
    ⟨_, hpg, ?_, ?_⟩, treeEls_wLeaf hpg hn hb32⟩
  · rw [wPage_count hn]; exact hn0
  · have hfl : pageFlags (wPage wid true ms ovf tail) = leafPageFlag := by
      rw [wPage_flags]; rfl
    unfold pageKey
    rw [if_pos (by rw [hfl]; rfl), (wPage_leaf (id := wid) (ovf := ovf) (tail := tail) hn0 hb32).2.2.2.2.1,
      msKey_of hn0]

/-- **A written branch page is a finished subtree** from its first key, over its children's
`sTree`s (of height `h`, within the entries' bounds, first keys the entries'): of height `h + 1`,
its leaf elements its children's in order. -/
theorem fTree_wBranch {P : Pages} {hwm : Nat} {hi : Option (List w8)} {h : Nat}
    (wid : w64) (ms : List InodeM) (ovf : w32) (tail : List w8) (Sc : Nat → List Nat)
    (hpg : P !! wid.toNat = some (wPage wid false ms ovf tail)) (h2 : 2 ≤ wid.toNat)
    (hlen : (wPage wid false ms ovf tail).length = (1 + ovf.toNat) * 4096)
    (hn2 : 2 ≤ ms.length) (hn : ms.length < 2 ^ 16)
    (hb : 16 + (pageBody true ms).length ≤ maxAllocSize) (hs : msSorted ms)
    (hk0 : ∀ m ∈ ms, 0 < m.key.length) (hkin : ∀ m ∈ ms, keyIn (some (msKey ms 0)) hi m.key)
    (hch : ∀ i (hix : i < ms.length), sTree P hwm ms[i].pgid.toNat
      (childLo (some (msKey ms 0)) (msKey ms) i) (childHi hi (msKey ms) ms.length i) h (Sc i))
    (hfirst : ∀ i (hix : i < ms.length), ∃ cpg, P !! ms[i].pgid.toNat = some cpg ∧
      0 < pageCount cpg ∧ pageKey cpg 0 = ms[i].key)
    (hd : subsDisj P wid.toNat (wPage wid false ms ovf tail) ms.length Sc)
    (hext : wid.toNat + (1 + ovf.toNat) ≤ hwm) :
    fTree P hwm wid.toNat (msKey ms 0) hi (h + 1) (nodePages wid.toNat ms.length Sc)
      (ms.flatMap fun m => treeEls P m.pgid.toNat) := by
  have hb32 : 16 + (pageBody true ms).length < 2 ^ 32 := by unfold maxAllocSize at hb; omega
  have hn0 : 0 < ms.length := by omega
  refine ⟨sTree_wBranch wid ms ovf tail Sc hpg h2 (by omega) hlen hn2 hn hb hs hk0 hkin hch hfirst
      hd hext, ⟨_, hpg, ?_, ?_⟩,
    treeEls_wBranch hpg hn hb32 Sc _ _ _ hch hd.own⟩
  · rw [wPage_count hn]; exact hn0
  · have hfl : pageFlags (wPage wid false ms ovf tail) = branchPageFlag := by
      rw [wPage_flags]; rfl
    unfold pageKey
    rw [if_neg (by rw [hfl]; decide), (wPage_branch (id := wid) (ovf := ovf) (tail := tail) hn0 hb32).2.2.2,
      msKey_of hn0]

end els

end Spill

end bbolt
end EtcdGrove
end Perennial
