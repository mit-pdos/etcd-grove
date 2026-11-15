/-
The spill's pure page facts (U9d, `notes/bbolt-proof-plan.md`): **a page `node.write` wrote**
(`encode (mkPageHdr id leaf ms.length ovf) ++ pageBody leaf ms ++ tail`) decodes element by
element to the inodes `ms` (`Model/Page`'s `pageInodes_writeInodes` is the round trip of the
whole list; here each element's position and sizes), and is a well-formed leaf (`leafWF`) or
branch (`branchWF`) page when its keys increase and its body fits `MaxAllocSize`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Tree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Spill

section written
variable [GooseExts]

/-- The bytes of a page `node.write` wrote: its header, its body, and the rest of the buffer. -/
def wPage (id : w64) (leaf : Bool) (ms : List InodeM) (ovf : w32) (tail : List w8) : List w8 :=
  encode (mkPageHdr id leaf ms.length ovf) ++ (pageBody leaf ms ++ tail)

theorem wPage_hdr (id : w64) (leaf : Bool) (ms : List InodeM) (ovf : w32) (tail : List w8) :
    pageHdr (wPage id leaf ms ovf tail) = mkPageHdr id leaf ms.length ovf := by
  unfold wPage; rw [pageHdr_bytes]

theorem wPage_count {id : w64} {leaf : Bool} {ms : List InodeM} {ovf : w32} {tail : List w8}
    (hn : ms.length < 2 ^ 16) : pageCount (wPage id leaf ms ovf tail) = ms.length := by
  simp only [pageCount, wPage_hdr, mkPageHdr]; word

theorem wPage_flags (id : w64) (leaf : Bool) (ms : List InodeM) (ovf : w32) (tail : List w8) :
    pageFlags (wPage id leaf ms ovf tail) = if leaf then leafPageFlag else branchPageFlag := by
  simp only [pageFlags, wPage_hdr, mkPageHdr]
  cases leaf <;> simp [leafPageFlag, branchPageFlag]

theorem wPage_id (id : w64) (leaf : Bool) (ms : List InodeM) (ovf : w32) (tail : List w8) :
    pageId (wPage id leaf ms ovf tail) = id.toNat := by
  simp only [pageId, wPage_hdr, mkPageHdr]

theorem wPage_overflow (id : w64) (leaf : Bool) (ms : List InodeM) (ovf : w32) (tail : List w8) :
    pageOverflow (wPage id leaf ms ovf tail) = ovf.toNat := by
  simp only [pageOverflow, wPage_hdr, mkPageHdr]

theorem wPage_length (id : w64) (leaf : Bool) (ms : List InodeM) (ovf : w32) (tail : List w8) :
    (wPage id leaf ms ovf tail).length = 16 + (pageBody true ms).length + tail.length := by
  simp [wPage, ByteEncoding.encode_length, pageBody_length]; omega

/-- Element `i` of a written leaf page. -/
theorem wPage_leafElem {id : w64} {ms : List InodeM} {ovf : w32} {tail : List w8} {i : Nat}
    (h1 : i < ms.length) :
    leafElem (wPage id true ms ovf tail) i = (leafElems ms)[i]'(by rw [leafElems_length]; exact h1) := by
  unfold leafElem wPage
  rw [bytesAt_hdr _ _ _ _ (by simp [elemOff]),
    show elemOff i - 16 = 16 * i by simp [elemOff], pageBody_leaf_elem ms tail i h1,
    ByteEncoding.decode_encode]

/-- Element `i` of a written branch page. -/
theorem wPage_branchElem {id : w64} {ms : List InodeM} {ovf : w32} {tail : List w8} {i : Nat}
    (h1 : i < ms.length) :
    branchElem (wPage id false ms ovf tail) i =
      (branchElems ms)[i]'(by rw [branchElems_length]; exact h1) := by
  unfold branchElem wPage
  rw [bytesAt_hdr _ _ _ _ (by simp [elemOff]),
    show elemOff i - 16 = 16 * i by simp [elemOff], pageBody_branch_elem ms tail i h1,
    ByteEncoding.decode_encode]

/-- **A written leaf page's element `i`**: its position, sizes, flags, key and value are inode
`i`'s. -/
theorem wPage_leaf {id : w64} {ms : List InodeM} {ovf : w32} {tail : List w8} {i : Nat}
    (h1 : i < ms.length) (hb : 16 + (pageBody true ms).length < 2 ^ 32) :
    leafPos (wPage id true ms ovf tail) i = dataOff ms i - (16 + 16 * i) ∧
    leafKsize (wPage id true ms ovf tail) i = ms[i].key.length ∧
    leafVsize (wPage id true ms ovf tail) i = ms[i].value.length ∧
    leafFlags (wPage id true ms ovf tail) i = ms[i].flags.toNat ∧
    leafKey (wPage id true ms ovf tail) i = ms[i].key ∧
    leafValue (wPage id true ms ovf tail) i = ms[i].value := by
  have hdo := dataOff_le ms i h1
  have hdg := dataOff_ge ms i
  have hk' : ms[i].kv.length = ms[i].key.length + ms[i].value.length := by simp [InodeM.kv]
  have he := wPage_leafElem (id := id) (ovf := ovf) (tail := tail) h1
  have hp : leafPos (wPage id true ms ovf tail) i = dataOff ms i - (16 + 16 * i) := by
    simp only [leafPos, he, leafElems, List.getElem_mapIdx]; word
  have hks : leafKsize (wPage id true ms ovf tail) i = ms[i].key.length := by
    simp only [leafKsize, he, leafElems, List.getElem_mapIdx]; word
  have hvs : leafVsize (wPage id true ms ovf tail) i = ms[i].value.length := by
    simp only [leafVsize, he, leafElems, List.getElem_mapIdx]; word
  refine ⟨hp, hks, hvs, ?_, ?_, ?_⟩
  · simp only [leafFlags, he, leafElems, List.getElem_mapIdx]
  · unfold leafKey
    rw [hp, hks]
    unfold wPage
    rw [bytesAt_hdr _ _ _ _ (by simp [elemOff]; omega),
      show elemOff i + (dataOff ms i - (16 + 16 * i)) - 16 = dataOff ms i - 16 by
        simp [elemOff]; omega,
      pageBody_key' true ms tail i h1]
  · unfold leafValue
    rw [hp, hks, hvs]
    unfold wPage
    rw [bytesAt_hdr _ _ _ _ (by simp [elemOff]; omega),
      show elemOff i + (dataOff ms i - (16 + 16 * i)) + ms[i].key.length - 16 =
        dataOff ms i - 16 + ms[i].key.length by simp [elemOff]; omega,
      pageBody_value' true ms tail i h1]

/-- **A written branch page's element `i`**: its position, key size, child and key are inode
`i`'s. -/
theorem wPage_branch {id : w64} {ms : List InodeM} {ovf : w32} {tail : List w8} {i : Nat}
    (h1 : i < ms.length) (hb : 16 + (pageBody true ms).length < 2 ^ 32) :
    branchPos (wPage id false ms ovf tail) i = dataOff ms i - (16 + 16 * i) ∧
    branchKsize (wPage id false ms ovf tail) i = ms[i].key.length ∧
    branchPgid (wPage id false ms ovf tail) i = ms[i].pgid.toNat ∧
    branchKey (wPage id false ms ovf tail) i = ms[i].key := by
  have hdo := dataOff_le ms i h1
  have hdg := dataOff_ge ms i
  have hk' : ms[i].kv.length = ms[i].key.length + ms[i].value.length := by simp [InodeM.kv]
  have he := wPage_branchElem (id := id) (ovf := ovf) (tail := tail) h1
  have hp : branchPos (wPage id false ms ovf tail) i = dataOff ms i - (16 + 16 * i) := by
    simp only [branchPos, he, branchElems, List.getElem_mapIdx]; word
  have hks : branchKsize (wPage id false ms ovf tail) i = ms[i].key.length := by
    simp only [branchKsize, he, branchElems, List.getElem_mapIdx]; word
  refine ⟨hp, hks, ?_, ?_⟩
  · simp only [branchPgid, he, branchElems, List.getElem_mapIdx]
  · unfold branchKey
    rw [hp, hks]
    unfold wPage
    rw [bytesAt_hdr _ _ _ _ (by simp [elemOff]; omega),
      show elemOff i + (dataOff ms i - (16 + 16 * i)) - 16 = dataOff ms i - 16 by
        simp [elemOff]; omega,
      pageBody_key' false ms tail i h1]

/-- The keys of `ms` increase strictly. -/
def msSorted (ms : List InodeM) : Prop :=
  ∀ i j (hi : i < j) (hj : j < ms.length), go.GoStringLt (ms[i]'(by omega)).key ms[j].key

/-- **A written leaf page is well-formed** (its own length, keys increasing, body within
`MaxAllocSize`). -/
theorem wPage_leafWF {id : w64} {ms : List InodeM} {ovf : w32} {tail : List w8}
    (hn : ms.length < 2 ^ 16) (hb : 16 + (pageBody true ms).length ≤ maxAllocSize)
    (hs : msSorted ms) :
    leafWF (wPage id true ms ovf tail) (wPage id true ms ovf tail).length := by
  have hb32 : 16 + (pageBody true ms).length < 2 ^ 32 := by unfold maxAllocSize at hb; omega
  have hc := wPage_count (id := id) (leaf := true) (ovf := ovf) (tail := tail) hn
  have hlen := wPage_length id true ms ovf tail
  have hbl := pageBody_length true ms
  refine ⟨Nat.le_refl _, ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
  · rw [hc, hlen]; simp only [elemOff]; omega
  · rw [hc] at hi
    obtain ⟨hp, hks, hvs, -, -, -⟩ := wPage_leaf (id := id) (ovf := ovf) (tail := tail) hi hb32
    have hdo := dataOff_le ms i hi
    have hdg := dataOff_ge ms i
    have hk' : ms[i].kv.length = ms[i].key.length + ms[i].value.length := by simp [InodeM.kv]
    rw [hp, hks, hvs, hlen]
    simp only [elemOff]
    constructor <;> omega
  · rw [hc] at hj
    obtain ⟨-, -, -, -, hki, -⟩ := wPage_leaf (id := id) (ovf := ovf) (tail := tail)
      (show i < ms.length by omega) hb32
    obtain ⟨-, -, -, -, hkj, -⟩ := wPage_leaf (id := id) (ovf := ovf) (tail := tail) hj hb32
    rw [hki, hkj]
    exact hs i j hij hj

/-- **A written branch page is well-formed** (an element, its own length, keys increasing,
children below `hwm`, body within `MaxAllocSize`). -/
theorem wPage_branchWF {id : w64} {ms : List InodeM} {ovf : w32} {tail : List w8} {hwm : Nat}
    (h0 : 0 < ms.length) (hn : ms.length < 2 ^ 16)
    (hb : 16 + (pageBody true ms).length ≤ maxAllocSize) (hs : msSorted ms)
    (hc : ∀ m ∈ ms, m.pgid.toNat < hwm) :
    branchWF (wPage id false ms ovf tail) (wPage id false ms ovf tail).length hwm := by
  have hb32 : 16 + (pageBody true ms).length < 2 ^ 32 := by unfold maxAllocSize at hb; omega
  have hcn := wPage_count (id := id) (leaf := false) (ovf := ovf) (tail := tail) hn
  have hlen := wPage_length id false ms ovf tail
  have hbl := pageBody_length true ms
  refine ⟨by rw [hcn]; exact h0, Nat.le_refl _, ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
  · rw [hcn, hlen]; simp only [elemOff]; omega
  · rw [hcn] at hi
    obtain ⟨hp, hks, hpg, -⟩ := wPage_branch (id := id) (ovf := ovf) (tail := tail) hi hb32
    have hdo := dataOff_le ms i hi
    have hdg := dataOff_ge ms i
    have hk' : ms[i].kv.length = ms[i].key.length + ms[i].value.length := by simp [InodeM.kv]
    rw [hp, hks, hpg, hlen]
    simp only [elemOff]
    refine ⟨by omega, by omega, hc _ (List.getElem_mem _)⟩
  · rw [hcn] at hj
    obtain ⟨-, -, -, hki⟩ := wPage_branch (id := id) (ovf := ovf) (tail := tail)
      (show i < ms.length by omega) hb32
    obtain ⟨-, -, -, hkj⟩ := wPage_branch (id := id) (ovf := ovf) (tail := tail) hj hb32
    rw [hki, hkj]
    exact hs i j hij hj

end written

end Spill

end bbolt
end EtcdGrove
end Perennial
