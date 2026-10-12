/-
A new, empty bucket (`CreateBucket`): its value (`emptyBV`, what `write` makes of an empty leaf
root) is a good inline bucket.
-/
module

public import Proof.go_etcd_io.bbolt.WriteBucket
public import Spec.go_etcd_io.bbolt.Bucket__write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- The value of a new, empty bucket: a zero header, and a leaf page with no element. -/
def emptyBV : List w8 :=
  List.replicate 16 (0 : w8) ++ [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]

section pure
variable [ext : FfiSyntax]

theorem writtenBucket_empty : writtenBucket ⟨W64 0, W64 0⟩ true [] [] [] = emptyBV := by
  unfold writtenBucket emptyBV writtenHdr
  simp [writtenElems, kvBytes, inBucketBytes, pageBytes, leBytes]

theorem emptyBV_facts : emptyBV.length = 32 ∧ inBucketRoot emptyBV = 0 ∧
    pageFlags (inlinePage emptyBV) = leafPageFlag ∧ pageCount (inlinePage emptyBV) = 0 ∧
    pageId (inlinePage emptyBV) = 0 ∧ (inlinePage emptyBV).length = 16 := by
  decide

theorem bvalOK_empty (pages : GMap Nat (List w8)) (hwm : Nat) : bvalOK pages hwm emptyBV := by
  obtain ⟨hl, hr, hf, hc, hi, hil⟩ := emptyBV_facts
  have hwf : leafWF (inlinePage emptyBV) (inlinePage emptyBV).length := by
    refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
    · rw [hc, hil]; decide
    · intro i hi'; rw [hc] at hi'; omega
    · intro i j _ hj; rw [hc] at hj; omega
  refine ⟨bucketWF.inline _ (by omega) hr hf (pageTreeWF.leaf _ _ hf hwf ?_), fun _ => ?_⟩
  · intro i hi'; rw [hc] at hi'; omega
  · exact ⟨hi, hf, hwf, by omega, fun i hi' => by rw [hc] at hi'; omega⟩

theorem wtxSub_trans (T1 T2 T3 : WTx) (h1 : wtxSub T1 T2) (h2 : wtxSub T2 T3) : wtxSub T1 T3 := by
  obtain ⟨a1, b1, c1, d1, s1, e1⟩ := h1
  obtain ⟨a2, b2, c2, d2, s2, e2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, fun b hb => d2 b (d1 b hb), s2, ?_⟩
  rw [e2, e1]

/-- A bucket with a root node, its inline page dropped: still clean. -/
theorem bktClean_pageNil (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hrn : B.bv.rootNode' ≠ null) :
    bktClean W hwm bl { B with bv := { B.bv with page' := null } } := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  exact ⟨fun _ h => absurd h hrn, c2, fun h => absurd h hrn, c4, c5, fun _ => rfl, c7, c8, c9, c10⟩

end pure

end bbolt
end EtcdGrove
end Perennial
