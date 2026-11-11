/-
`WriteInodeToPage`'s pure lemmas (U1 of `notes/bbolt-proof-plan.md`): the bytes after the header
of a page after the first `j` iterations of its loop, over arbitrary initial bytes (`rest`). The
element and data lemmas are adapted from Perennial's `unsafememory/Pages.lean` (there over zeros).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Page

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.common

section model
variable [GooseExts]

/-- The elements written by the first `j` iterations of `WriteInodeToPage`. -/
def elemsPrefix (leaf : Bool) (ms : List InodeM) (j : Nat) : List w8 :=
  if leaf then ((leafElems ms).take j).flatMap encode else ((branchElems ms).take j).flatMap encode

theorem elemsPrefix_zero (leaf : Bool) (ms : List InodeM) : elemsPrefix leaf ms 0 = [] := by
  unfold elemsPrefix; split <;> simp

theorem elemsPrefix_length (leaf : Bool) (ms : List InodeM) (j : Nat) (h : j ≤ ms.length) :
    (elemsPrefix leaf ms j).length = 16 * j := by
  unfold elemsPrefix
  split
  · rw [flatMap_encode_length', List.length_take, leafElems_length, Nat.min_eq_left h, Nat.mul_comm]
  · rw [flatMap_encode_length', List.length_take, branchElems_length, Nat.min_eq_left h,
      Nat.mul_comm]

theorem elemsPrefix_full (leaf : Bool) (ms : List InodeM) :
    elemsPrefix leaf ms ms.length = elemBytes leaf ms := by
  unfold elemsPrefix elemBytes
  split
  · rw [List.take_of_length_le (by rw [leafElems_length]; exact Nat.le_refl _)]
  · rw [List.take_of_length_le (by rw [branchElems_length]; exact Nat.le_refl _)]

theorem elemsPrefix_succ_leaf (ms : List InodeM) (j : Nat) (h : j < ms.length) :
    elemsPrefix true ms (j + 1) =
      elemsPrefix true ms j ++ encode ((leafElems ms)[j]'(by rw [leafElems_length]; exact h)) := by
  simp only [elemsPrefix, ite_true, List.take_add_one,
    List.getElem?_eq_getElem (show j < (leafElems ms).length by rw [leafElems_length]; exact h),
    Option.toList_some, List.flatMap_append, List.flatMap_singleton]

theorem elemsPrefix_succ_branch (ms : List InodeM) (j : Nat) (h : j < ms.length) :
    elemsPrefix false ms (j + 1) =
      elemsPrefix false ms j ++
        encode ((branchElems ms)[j]'(by rw [branchElems_length]; exact h)) := by
  simp only [elemsPrefix, Bool.false_eq_true, ite_false, List.take_add_one,
    List.getElem?_eq_getElem (show j < (branchElems ms).length by rw [branchElems_length]; exact h),
    Option.toList_some, List.flatMap_append, List.flatMap_singleton]

theorem leafElems_getElem (ms : List InodeM) (j : Nat) (h : j < (leafElems ms).length) :
    (leafElems ms)[j] = ⟨(ms[j]'(by rw [leafElems_length] at h; exact h)).flags,
      W32 ((dataOff ms j - (16 + 16 * j) : Nat) : Int),
      W32 ((ms[j]'(by rw [leafElems_length] at h; exact h)).key.length : Int),
      W32 ((ms[j]'(by rw [leafElems_length] at h; exact h)).value.length : Int)⟩ := by
  simp [leafElems, List.getElem_mapIdx]

theorem branchElems_getElem (ms : List InodeM) (j : Nat) (h : j < (branchElems ms).length) :
    (branchElems ms)[j] = ⟨W32 ((dataOff ms j - (16 + 16 * j) : Nat) : Int),
      W32 ((ms[j]'(by rw [branchElems_length] at h; exact h)).key.length : Int),
      (ms[j]'(by rw [branchElems_length] at h; exact h)).pgid⟩ := by
  simp [branchElems, List.getElem_mapIdx]

/-- Writing `X` right after the prefix `A`, over the bytes `T`. -/
theorem replaceBytes_after (A T X : List w8) :
    replaceBytes (A ++ T) A.length X = A ++ X ++ T.drop X.length := by
  unfold replaceBytes
  rw [List.take_left' rfl, show A.length + X.length = A.length + X.length from rfl,
    ← List.drop_drop, List.drop_left]

/-- The untouched element bytes, one element further. -/
theorem restElems_step (rest : List w8) (n j : Nat) (hj : j < n) :
    ((rest.drop (16 * j)).take (16 * (n - j))).drop 16 =
      (rest.drop (16 * (j + 1))).take (16 * (n - (j + 1))) := by
  rw [List.drop_take, List.drop_drop]
  congr 1; omega

/-- The data area, one inode further: `dataBytes (ms.take (j+1))` and the rest. -/
theorem dataArea_step (ms : List InodeM) (R : List w8) (j : Nat) (hj : j < ms.length) :
    dataBytes (ms.take j) ++ (ms[j].key ++ ms[j].value) ++
        (R.drop (dataBytes (ms.take j)).length).drop (ms[j].key ++ ms[j].value).length =
      dataBytes (ms.take (j + 1)) ++ R.drop (dataBytes (ms.take (j + 1))).length := by
  rw [dataBytes_take_succ ms j hj, List.drop_drop, List.length_append]
  simp [InodeM.kv]

/-- The element region after iteration `j` writes leaf element `j`. -/
theorem elemsRegion_step_leaf (ms : List InodeM) (rest : List w8) (j : Nat) (hj : j < ms.length) :
    replaceBytes (elemsPrefix true ms j ++ (rest.drop (16 * j)).take (16 * (ms.length - j)))
        (16 * j) (encode ((leafElems ms)[j]'(by rw [leafElems_length]; exact hj))) =
      elemsPrefix true ms (j + 1) ++
        (rest.drop (16 * (j + 1))).take (16 * (ms.length - (j + 1))) := by
  have h := replaceBytes_after (elemsPrefix true ms j)
    ((rest.drop (16 * j)).take (16 * (ms.length - j)))
    (encode ((leafElems ms)[j]'(by rw [leafElems_length]; exact hj)))
  rw [elemsPrefix_length _ _ _ (by omega)] at h
  rw [h, ByteEncoding.encode_length, restElems_step _ _ _ hj, elemsPrefix_succ_leaf _ _ hj]

/-- The element region after iteration `j` writes branch element `j`. -/
theorem elemsRegion_step_branch (ms : List InodeM) (rest : List w8) (j : Nat) (hj : j < ms.length) :
    replaceBytes (elemsPrefix false ms j ++ (rest.drop (16 * j)).take (16 * (ms.length - j)))
        (16 * j) (encode ((branchElems ms)[j]'(by rw [branchElems_length]; exact hj))) =
      elemsPrefix false ms (j + 1) ++
        (rest.drop (16 * (j + 1))).take (16 * (ms.length - (j + 1))) := by
  have h := replaceBytes_after (elemsPrefix false ms j)
    ((rest.drop (16 * j)).take (16 * (ms.length - j)))
    (encode ((branchElems ms)[j]'(by rw [branchElems_length]; exact hj)))
  rw [elemsPrefix_length _ _ _ (by omega)] at h
  rw [h, ByteEncoding.encode_length, restElems_step _ _ _ hj, elemsPrefix_succ_branch _ _ hj]

theorem dataOff_zero (ms : List InodeM) : dataOff ms 0 = 16 + 16 * ms.length := by
  simp [dataOff, dataBytes]

theorem dataOff_full (ms : List InodeM) :
    dataOff ms ms.length = 16 + (pageBody true ms).length := by
  simp only [dataOff, List.take_length, pageBody_length]; omega

end model

end bbolt
end EtcdGrove
end Perennial
