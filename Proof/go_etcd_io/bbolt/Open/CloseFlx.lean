/-
The writer side's half of the synced freelist page (session S4, `wBytesX`'s `X = flxS …`): its
slots are `W` slots inside the file holding whole pages (`wdbOK`'s `flCurOK`), what joining it with
the store's half needs (`Close`'s hand-back, `wBytes_joinX`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WBytesX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk]
set_option linter.unusedSectionVars false

private theorem extentBytes_overflow_c (wb : Nat → List w8) (f : Nat) (h16 : 16 ≤ (wb f).length) :
    pageOverflow (extentBytes wb f) = pageOverflow (wb f) := by
  unfold pageOverflow pageHdr bytesAt
  congr 3
  unfold extentBytes
  rw [show 1 + pageOverflow (wb f) = (pageOverflow (wb f)) + 1 by omega, List.range'_succ,
    List.flatMap_cons, List.drop_zero, List.drop_zero,
    List.take_append_of_le_length h16]

/-- **The writer side's freelist-page slots are `W` slots inside the file, whole pages.** -/
theorem wdbOK_flxS (w : WDb) (hok : wdbOK w) :
    ∀ s ∈ flxS w.C w.fl w.wb, s ∈ w.W ∧ 4096 * (s + 1) ≤ w.m.size ∧ (w.wb s).length = 4096 := by
  intro s hs
  unfold flxS at hs
  rcases hf : w.C.flpg with _ | f
  · rw [hf] at hs; cases hs
  rw [hf] at hs
  by_cases hp : f ∈ pendSlots w.fl
  · simp only [hp, ↓reduceIte] at hs; cases hs
  simp only [hp, ↓reduceIte] at hs
  unfold flExt at hs
  rw [List.mem_range'_1] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, htx, hhwm, hmap, hsmall, hslots, hfree⟩ := hok
  have hlen15 := hfree.2.2.2.1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := h6 f hf f hf
  have hsz : w.C.hwm * 4096 ≤ w.m.size := h3
  have hinW : ∀ t, f ≤ t → t < f + (1 + pageOverflow (extentBytes w.wb f)) → t ∈ w.W := by
    intro t a b
    have hnotAll := (c9 t a b).2
    have hnotPend : t ∉ pendSlots w.fl := by
      intro h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      apply hnotAll
      have : W64 (x.toNat : Int) = x := BitVec.eq_of_toNat_eq (toNat_W64_of_lt x.toNat x.isLt)
      rw [this]
      exact List.mem_append_right _ hx
    have hnotTree : t ∉ treeSlots w.C := fun h => (c9 t a b).1 ((mem_pagesSlots_iff _ _).1 h)
    refine (h4 t).2 ⟨by omega, ?_, hnotTree, hnotPend⟩
    have : t < w.m.size / 4096 := by
      rw [Nat.lt_div_iff_mul_lt (by omega)]; omega
    exact Nat.lt_of_lt_of_le this (Nat.div_le_div_right (Nat.le_max_right _ _))
  have hf16 : 16 ≤ (w.wb f).length := by
    rw [hlen15 f (hinW f (Nat.le_refl _) (by omega)) (by omega)]; omega
  have hov := extentBytes_overflow_c w.wb f hf16
  rw [hov] at c2 hinW
  have hin := hinW s hs.1 hs.2
  exact ⟨hin, by omega, hlen15 s hin (by omega)⟩

end pure

end bbolt
end EtcdGrove
end Perennial
