/-
A `pwrite` inside the file that wrote all of its data or nothing (U10, `writeMeta`'s D22 case):
the file's size is unchanged and the range's bytes are the data or the old ones.
-/
module

public import GooseLang.Ext.OsFs.Write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

theorem pwSize_inside (sz off j : Nat) (n : Nat) (hj : j ≤ n) (h : off + n ≤ sz) :
    pwSize sz off j = sz := by
  unfold pwSize; split <;> omega

/-- **The range after an all-or-nothing `pwrite` inside the file**: the old bytes (`j = 0`) or the
data (`j = data.length`). -/
theorem pwBytes_inside_fst (sz off : Nat) (data : List w8) (j : Nat) (xs : List (w8 × Bool))
    (h : off + data.length ≤ sz) (hx : xs.length = data.length) (hj : j = 0 ∨ j = data.length) :
    (pwBytes sz off data j xs).map Prod.fst = (if j = 0 then xs.map Prod.fst else data) := by
  have hs : pwSize sz off j = sz := pwSize_inside sz off j data.length (by omega) h
  have hm1 : min off sz = off := by omega
  have hm2 : min (off + data.length) sz = off + data.length := by omega
  unfold pwBytes
  rw [hs, hm1, hm2, show off + data.length - off = data.length by omega]
  apply List.ext_getElem
  · split <;> simp [hx]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    unfold pwByte
    rcases hj with rfl | rfl
    · simp only [↓reduceIte, List.getElem_map]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · by_cases h0 : data.length = 0
      · omega
      · simp only [h0, ↓reduceIte]
        rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

end bbolt
end EtcdGrove
end Perennial
