/-
U7j (`notes/bbolt-proof-plan.md`): **the value `CreateBucket` writes** (`bucket.write()` of
`Bucket{InBucket: &InBucket{}, rootNode: &node{isLeaf: true}}`, as `Bucket.write.spec` gives it
for no inodes): the empty inline bucket `emptyBktVal ib` (header `ib` of root `0`, then a leaf page
of id `0` and no element). Its facts: an inline value (`inBucketRoot = 0`) of 32 bytes, a good
inline page (`inlineGood`) of no entry, well-formed and bounded (`bvalOK`), holding no data
(`bktOfPage = ∅`) and no page (`bucketHas`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.WrittenPage
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Model.TreeData

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Spill

section createbktval
variable [GooseExts]

/-- The value `b.write()` makes of a bucket with the header `ib` and an empty root leaf. -/
def emptyBktVal (ib : InBucket) : List w8 :=
  encode ib ++ encode (hdrWritten ⟨W64 0, W16 0, W16 0, W32 0⟩ true ([] : List InodeM).length) ++
    pageBody true []

theorem emptyBktVal_inlinePage (ib : InBucket) :
    inlinePage (emptyBktVal ib) = wPage (W64 0) true [] (W32 0) [] := by
  unfold inlinePage emptyBktVal wPage bucketHeaderSize
  rw [List.append_assoc, List.drop_left' (by simp [ByteEncoding.encode_length]), List.append_nil]
  rfl

theorem emptyBktVal_root (ib : InBucket) (h0 : ib.root' = W64 0) :
    inBucketRoot (emptyBktVal ib) = 0 := by
  unfold inBucketRoot inBucketOf emptyBktVal bytesAt
  rw [List.append_assoc, List.drop_zero, List.take_left' (by simp [ByteEncoding.encode_length]),
    ByteEncoding.decode_encode, h0]
  rfl

theorem emptyBktVal_length (ib : InBucket) : (emptyBktVal ib).length = 32 := by
  simp [emptyBktVal, ByteEncoding.encode_length, pageBody_length, dataBytes]

theorem emptyPage_count : pageCount (wPage (W64 0) true [] (W32 0) []) = 0 :=
  wPage_count (by simp)

theorem emptyPage_length : (wPage (W64 0) true [] (W32 0) []).length = 16 := by
  rw [wPage_length]; simp [pageBody_length, dataBytes]

/-- **A good inline page.** -/
theorem emptyBktVal_good (ib : InBucket) : inlineGood (inlinePage (emptyBktVal ib)) := by
  rw [emptyBktVal_inlinePage]
  refine ⟨by rw [wPage_id]; rfl, by rw [wPage_flags]; rfl, ?_, by rw [emptyPage_length]; exact Nat.le_refl _, ?_⟩
  · refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
    · rw [emptyPage_count, emptyPage_length]; unfold elemOff; omega
    · intro i hi; rw [emptyPage_count] at hi; omega
    · intro i j _ hj; rw [emptyPage_count] at hj; omega
  · intro i hi; rw [emptyPage_count] at hi; omega

theorem emptyBktVal_bnd (ib : InBucket) : inlineBnd (inlinePage (emptyBktVal ib)) := by
  intro j hj; rw [emptyBktVal_inlinePage, emptyPage_count] at hj; omega

/-- **A well-formed bucket value.** -/
theorem emptyBktVal_wf (P : Pages) (hwm : Nat) (ib : InBucket) (h0 : ib.root' = W64 0) :
    bucketWF P hwm (emptyBktVal ib) := by
  have hg := emptyBktVal_good ib
  refine bucketWF.inline _ (by rw [emptyBktVal_length]; omega) (emptyBktVal_root ib h0) hg.2.1 ?_
  refine pageTreeWF.leaf _ _ hg.2.1 hg.2.2.1 ?_
  intro i hi; rw [emptyBktVal_inlinePage, emptyPage_count] at hi; omega

/-- **`nodeClean`'s value facts** for the new entry. -/
theorem emptyBktVal_ok (P : Pages) (hwm : Nat) (ib : InBucket) (h0 : ib.root' = W64 0) :
    bvalOK P hwm (emptyBktVal ib) :=
  ⟨emptyBktVal_wf P hwm ib h0, fun _ => ⟨emptyBktVal_good ib, emptyBktVal_bnd ib⟩,
    fun h => absurd (emptyBktVal_root ib h0) h⟩

/-- **No data.** -/
theorem emptyBktVal_data (P : Pages) (ib : InBucket) (h0 : ib.root' = W64 0) :
    bktOfPage P (emptyBktVal ib) = ∅ := by
  unfold bktOfPage bktEntries bktLeaves
  rw [if_pos (emptyBktVal_root ib h0)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold leafEnts
  rw [emptyBktVal_inlinePage, emptyPage_count]
  rfl

/-- **No page.** -/
theorem emptyBktVal_noHas (P : Pages) (ib : InBucket) (h0 : ib.root' = W64 0) (d : Nat) :
    ¬ bucketHas P (emptyBktVal ib) d := by
  have hg := emptyBktVal_good ib
  intro h
  cases h with
  | file _ _ hr' _ => exact hr' (emptyBktVal_root ib h0)
  | inline _ _ _ hp =>
    cases hp with
    | child _ _ _ hfl _ _ =>
      rw [hg.2.1] at hfl; simp [branchPageFlag, leafPageFlag] at hfl
    | bucket _ i _ _ hi _ _ =>
      rw [emptyBktVal_inlinePage, emptyPage_count] at hi; omega

end createbktval

end Write

end bbolt
end EtcdGrove
end Perennial
