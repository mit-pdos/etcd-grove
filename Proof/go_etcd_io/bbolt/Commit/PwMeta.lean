/-
A `pwrite` inside the file that wrote all of its data or nothing (U10, `writeMeta`'s D22 case):
the file's size is unchanged and the range's bytes are the data or the old ones.
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

theorem pwSize_inside (sz off j : Nat) (n : Nat) (hj : j ≤ n) (h : off + n ≤ sz) :
    pwSize sz off j = sz := by
  unfold pwSize; split <;> omega

/-- A write inside the file (of at most `n` bytes landed) leaves its size and mappings. -/
theorem pwPost_inside (m : OsMeta) (off n a k : Nat) (hk : k ≤ n) (h : off + n ≤ m.size) :
    (pwPost m off a k).size = m.size ∧ (pwPost m off a k).maps = m.maps :=
  ⟨pwSize_inside m.size off k n hk h, by simp only [pwPost, announce_maps]⟩

/-- **The values after an all-or-nothing write inside the file** (`WriteAt.specExt`'s `pwValsG`):
the old bytes (`j = 0`) or the data (`j = data.length`). -/
theorem pwValsG_inside (sz off : Nat) (data : List w8) (j : Nat) (xs : List ByteG)
    (h : off + data.length ≤ sz) (hx : xs.length = data.length) (hj : j = 0 ∨ j = data.length) :
    pwValsG sz off data j xs = (if j = 0 then xs.map Prod.fst else data) := by
  have hs : pwSize sz off j = sz := pwSize_inside sz off j data.length (by omega) h
  have hm1 : min off sz = off := by omega
  have hm2 : min (off + data.length) sz = off + data.length := by omega
  unfold pwValsG
  rw [hs, hm1, hm2, show off + data.length - off = data.length by omega]
  apply List.ext_getElem
  · split <;> simp [hx]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    unfold pwByteG
    rcases hj with rfl | rfl
    · simp only [↓reduceIte, List.getElem_map]
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    · by_cases h0 : data.length = 0
      · omega
      · simp only [h0, ↓reduceIte]
        rw [ite_eq_left (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- **The range after an all-or-nothing `WriteAt` inside the file** (`WriteAt.spec`'s `os.PwOut`):
the old bytes (`j = 0`) or the data (`j = data.length`). -/
theorem pwOut_inside_fst (m : OsMeta) (off : Nat) (data : List w8) (j : Nat) (xs ys : List ByteG)
    (h : off + data.length ≤ m.size) (hx : xs.length = data.length)
    (hj : j = 0 ∨ j = data.length) (hp : os.PwOut m off data j xs ys) :
    ys.map Prod.fst = (if j = 0 then xs.map Prod.fst else data) := by
  have hs : pwSize m.size off j = m.size := pwSize_inside m.size off j data.length (by omega) h
  obtain ⟨hl, hb⟩ := hp
  rw [hs, show min (off + data.length) m.size - off = data.length by omega] at hl
  apply List.ext_getElem
  · split <;> simp [hx, hl]
  · intro i h1 h2
    simp only [List.length_map] at h1
    rw [List.getElem_map, (hb i h1).1]
    unfold pwByte
    rcases hj with rfl | rfl
    · simp only [↓reduceIte, List.getElem_map]
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    · by_cases h0 : data.length = 0
      · omega
      · simp only [h0, ↓reduceIte]
        rw [ite_eq_left (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega), Option.getD_some]

end bbolt
end EtcdGrove
end Perennial
