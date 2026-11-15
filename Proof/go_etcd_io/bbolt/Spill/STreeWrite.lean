/-
The spill's pure tree facts (U9d, `notes/bbolt-proof-plan.md`), part 6: **a page `node.write`
wrote is an `sTree`** over its entries' subtrees: a branch over its children's `sTree`s
(`sTree_wBranch`), a leaf over its nested buckets' values (`sTree_wLeaf`). What a spilled node's
page is, once its children are written (`node.spill`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.STreeBuild
public import Proof.go_etcd_io.bbolt.Spill.WrittenPage

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Spill

section wtree
variable [GooseExts]

/-- The key of inode `j` (empty past the end). -/
def msKey (ms : List InodeM) (j : Nat) : List w8 := (ms[j]?.map InodeM.key).getD []

theorem msKey_of {ms : List InodeM} {j : Nat} (h : j < ms.length) : msKey ms j = ms[j].key := by
  simp [msKey, List.getElem?_eq_getElem h]

theorem childLo_congr {lo : Option (List w8)} {f g : Nat → List w8} {i : Nat}
    (h : i ≠ 0 → f i = g i) : childLo lo f i = childLo lo g i := by
  unfold childLo
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi, h hi]

theorem childHi_congr {hi : Option (List w8)} {f g : Nat → List w8} {n i : Nat}
    (h : i + 1 < n → f (i + 1) = g (i + 1)) : childHi hi f n i = childHi hi g n i := by
  unfold childHi
  by_cases hn : i + 1 < n
  · simp [hn, h hn]
  · simp [hn]

/-- **A written branch page over its children's `sTree`s** (of height `h`, within the entries'
bounds, first keys the entries') is an `sTree` of height `h + 1`. -/
theorem sTree_wBranch {P : Pages} {hwm : Nat} {lo hi : Option (List w8)} {h : Nat}
    (wid : w64) (ms : List InodeM) (ovf : w32) (tail : List w8) (Sc : Nat → List Nat)
    (hpg : P !! wid.toNat = some (wPage wid false ms ovf tail)) (h2 : 2 ≤ wid.toNat)
    (hlt : wid.toNat < hwm)
    (hlen : (wPage wid false ms ovf tail).length = (1 + ovf.toNat) * 4096)
    (hn2 : 2 ≤ ms.length) (hn : ms.length < 2 ^ 16)
    (hb : 16 + (pageBody true ms).length ≤ maxAllocSize) (hs : msSorted ms)
    (hk0 : ∀ m ∈ ms, 0 < m.key.length) (hkin : ∀ m ∈ ms, keyIn lo hi m.key)
    (hch : ∀ i (hix : i < ms.length), sTree P hwm ms[i].pgid.toNat (childLo lo (msKey ms) i)
      (childHi hi (msKey ms) ms.length i) h (Sc i))
    (hfirst : ∀ i (hix : i < ms.length), ∃ cpg, P !! ms[i].pgid.toNat = some cpg ∧
      0 < pageCount cpg ∧ pageKey cpg 0 = ms[i].key)
    (hd : subsDisj P wid.toNat (wPage wid false ms ovf tail) ms.length Sc)
    (hext : wid.toNat + (1 + ovf.toNat) ≤ hwm) :
    sTree P hwm wid.toNat lo hi (h + 1) (nodePages wid.toNat ms.length Sc) := by
  have hb32 : 16 + (pageBody true ms).length < 2 ^ 32 := by unfold maxAllocSize at hb; omega
  have hc := wPage_count (id := wid) (leaf := false) (ovf := ovf) (tail := tail) hn
  have hfl : pageFlags (wPage wid false ms ovf tail) = branchPageFlag := by
    rw [wPage_flags]; rfl
  have hel := fun i (hi : i < ms.length) =>
    wPage_branch (id := wid) (ovf := ovf) (tail := tail) hi hb32
  have hkey : ∀ j, j < ms.length → branchKey (wPage wid false ms ovf tail) j = msKey ms j :=
    fun j hj => by rw [(hel j hj).2.2.2, msKey_of hj]
  have hd' : subsDisj P wid.toNat (wPage wid false ms ovf tail)
      (pageCount (wPage wid false ms ovf tail)) Sc := by rw [hc]; exact hd
  have Hs := sTree_branch (P := P) (hwm := hwm) (id := wid.toNat) (lo := lo) (hi := hi) (h := h)
    (pg := wPage wid false ms ovf tail) Sc hpg hfl h2 hlt (wPage_id _ _ _ _ _)
    (by rw [hlen, wPage_overflow])
    (by rw [show (wPage wid false ms ovf tail).length = (wPage wid false ms ovf tail).length from rfl]
        exact wPage_branchWF (by omega) hn hb hs fun m hm => by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
          obtain ⟨cpg, hcp, -⟩ := hfirst i hi
          have := (hch i hi).ext _ ((((hch i hi).has _)).1 (treeHas.root _ cpg hcp)) cpg hcp
          omega)
    ⟨fun hl => by rw [hfl] at hl; simp [branchPageFlag, leafPageFlag] at hl,
      fun _ i hi => by rw [hc] at hi; rw [(hel i hi).2.1]; exact hk0 _ (List.getElem_mem _)⟩
    (by rw [hc]; exact hn2)
    (fun i hi => by rw [hc] at hi; rw [(hel i hi).2.2.2]; exact hkin _ (List.getElem_mem _))
    (fun i hi => by
      rw [hc] at hi
      rw [(hel i hi).2.2.1]
      rw [childLo_congr (g := msKey ms) (fun _ => hkey i hi),
        childHi_congr (g := msKey ms) (fun h1 => hkey (i + 1) (by rw [hc] at h1; exact h1)), hc]
      exact hch i hi)
    (fun i hi => by
      rw [hc] at hi
      rw [(hel i hi).2.2.1, (hel i hi).2.2.2]
      exact hfirst i hi)
    hd' (by rw [wPage_overflow]; exact hext)
  rw [hc] at Hs
  exact Hs

/-- **A written leaf page over its nested buckets' values** is an `sTree` of height `0`. -/
theorem sTree_wLeaf {P : Pages} {hwm : Nat} {lo hi : Option (List w8)}
    (wid : w64) (ms : List InodeM) (ovf : w32) (tail : List w8) (Sb : Nat → List Nat)
    (hpg : P !! wid.toNat = some (wPage wid true ms ovf tail)) (h2 : 2 ≤ wid.toNat)
    (hlt : wid.toNat < hwm)
    (hlen : (wPage wid true ms ovf tail).length = (1 + ovf.toNat) * 4096)
    (hn : ms.length < 2 ^ 16)
    (hb : 16 + (pageBody true ms).length ≤ maxAllocSize) (hs : msSorted ms)
    (hk0 : ∀ m ∈ ms, 0 < m.key.length) (hkin : ∀ m ∈ ms, keyIn lo hi m.key)
    (hbv : ∀ i (hix : i < ms.length), ms[i].flags.toNat % 2 = bucketLeafFlag →
      bvalS P hwm ms[i].value (Sb i))
    (hb0 : ∀ i (hix : i < ms.length), ms[i].flags.toNat % 2 ≠ bucketLeafFlag → Sb i = [])
    (hd : subsDisj P wid.toNat (wPage wid true ms ovf tail) ms.length Sb)
    (hext : wid.toNat + (1 + ovf.toNat) ≤ hwm) :
    sTree P hwm wid.toNat lo hi 0 (nodePages wid.toNat ms.length Sb) := by
  have hb32 : 16 + (pageBody true ms).length < 2 ^ 32 := by unfold maxAllocSize at hb; omega
  have hc := wPage_count (id := wid) (leaf := true) (ovf := ovf) (tail := tail) hn
  have hfl : pageFlags (wPage wid true ms ovf tail) = leafPageFlag := by
    rw [wPage_flags]; rfl
  have hel := fun i (hi : i < ms.length) =>
    wPage_leaf (id := wid) (ovf := ovf) (tail := tail) hi hb32
  have hd' : subsDisj P wid.toNat (wPage wid true ms ovf tail)
      (pageCount (wPage wid true ms ovf tail)) Sb := by rw [hc]; exact hd
  have Hs := sTree_leaf (P := P) (hwm := hwm) (id := wid.toNat) (lo := lo) (hi := hi)
    (pg := wPage wid true ms ovf tail) Sb hpg hfl h2 hlt (wPage_id _ _ _ _ _)
    (by rw [hlen, wPage_overflow]) (wPage_leafWF hn hb hs)
    ⟨fun _ i hi => by
        rw [hc] at hi
        obtain ⟨-, hks, -, hfg, -, hv⟩ := hel i hi
        refine ⟨by rw [hks]; exact hk0 _ (List.getElem_mem _), fun hbf hr => ?_⟩
        rw [hfg] at hbf
        rw [hv] at hr ⊢
        rcases (hbv i hi hbf).2 with ⟨-, -, hg⟩ | ⟨hr', -⟩
        · exact hg
        · exact absurd hr hr',
      fun hb' => by rw [hfl] at hb'; simp [branchPageFlag, leafPageFlag] at hb'⟩
    (fun i hi => by rw [hc] at hi; rw [(hel i hi).2.2.2.2.1]; exact hkin _ (List.getElem_mem _))
    (fun i hi hbf => by
      rw [hc] at hi
      rw [(hel i hi).2.2.2.1] at hbf
      rw [(hel i hi).2.2.2.2.2]
      exact hbv i hi hbf)
    (fun i hi hbf => by
      rw [hc] at hi
      rw [(hel i hi).2.2.2.1] at hbf
      exact hb0 i hi hbf)
    hd' (by rw [wPage_overflow]; exact hext)
  rw [hc] at Hs
  exact Hs

end wtree

end Spill

end bbolt
end EtcdGrove
end Perennial
