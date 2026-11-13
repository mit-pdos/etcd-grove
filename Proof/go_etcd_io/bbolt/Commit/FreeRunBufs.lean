/-
**No dirty page on the freed freelist page's run** (U10o, for `Tx.Commit_err`'s `hbx`): every
buffer slot was free in the spill's starting freelist or at or above the committed mark
(`Bucket.spill.spec`'s last conjunct); the synced freelist page's run, read at the start, is in
no list of the starting freelist and below the mark (`flCurOK`). The run is measured by the
page's header at the free (`w'.wb f`): the same page, given its first slot's bytes kept.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.FreeFlPure
import Proof.go_etcd_io.bbolt.Txn.WJoin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem cm_bufs_off_flrun (w w' : WDb) (S : List Nat) (f : Nat) (hok : wdbOK w)
    (hf : w.C.flpg = some f) (hwb : w'.wb f = w.wb f)
    (hsrc : ∀ s ∈ S, W64 s ∈ w.fl.free ∨ w.C.hwm ≤ s) :
    ∀ s ∈ S, ¬ (f ≤ s ∧ s < f + (1 + pageOverflow (w'.wb f))) := by
  intro s hs ⟨h1, h2⟩
  have h16 := wb_header w hok f hf
  have hov := extentBytes_overflow w.wb f h16
  rw [hwb] at h2
  obtain ⟨-, c2, -, -, -, -, -, -, c9, -⟩ := hok.2.2.2.2.2.1 f hf f hf
  rw [hov] at c2 c9
  rcases hsrc s hs with hx | hx
  · exact (c9 s h1 h2).2 (List.mem_append_left _ hx)
  · omega

/-- The synced freelist page's first slot is a `W` slot (in no list, not a tree slot, below the
mark, so inside the file). -/
theorem cm_flpg_W (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) : f ∈ w.W := by
  have h16 := wb_header w hok f hf
  have hov := extentBytes_overflow w.wb f h16
  have h3 : w.C.hwm * 4096 ≤ w.m.size := hok.2.2.1
  have h4 := hok.2.2.2.1
  obtain ⟨c1, c2, -, -, -, -, -, -, c9, -⟩ := hok.2.2.2.2.2.1 f hf f hf
  rw [hov] at c2 c9
  have hlt : f < f + (1 + pageOverflow (w.wb f)) := by omega
  obtain ⟨hc, hall⟩ := c9 f (Nat.le_refl _) hlt
  refine (h4 f).2 ⟨c1, ?_, fun h => hc ((mem_pagesSlots_iff _ _).1 h), fun hs => ?_⟩
  · have : f < w.m.size / 4096 := by
      rw [Nat.lt_div_iff_mul_lt (by omega)]; omega
    exact Nat.lt_of_lt_of_le this (Nat.div_le_div_right (Nat.le_max_right _ _))
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    apply hall
    have : W64 (x.toNat : Int) = x := BitVec.eq_of_toNat_eq (toNat_W64_of_lt x.toNat x.isLt)
    rw [this]
    exact List.mem_append_right _ hx

end pure

end bbolt
end EtcdGrove
end Perennial
