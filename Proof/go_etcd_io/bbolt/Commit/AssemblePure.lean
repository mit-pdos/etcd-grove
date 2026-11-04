/-
`Commit`'s pure steps (U10g of `notes/bbolt-proof-plan.md`): from one callee's post to the next
callee's premises.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX
public import Proof.go_etcd_io.bbolt.Inv.Locks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **`rebalance`'s post is `spill`'s pre** (the leaves at one depth: `rtOK`). -/
theorem spillPre_of_rebalOK (X X1 : WX) (fl fl1 : FLPg) (txid : w64)
    (h : rebalOK X X1 fl fl1 txid) : spillPre X1 fl1 := by
  obtain ⟨h1, -, hv, -, -, -, h7, -, h9, -, h11⟩ := h
  refine ⟨h1, h7, fun bl hb => leafDepthOK_rt X1 bl (h9 bl hb), h9, fun s hs => ?_⟩
  rw [hv] at hs
  exact h11 s hs

/-- **`commitFreelist`'s id bound**: the freelist's ids (distinct, below the high-water mark) are
fewer than `2^48` when the mark is. -/
theorem cm_allIds_lt (w : WDb) (hok : wdbOK w) (hwf : w.fl.WF) (hh : w.C.hwm < 2 ^ 48) :
    w.fl.allIds.length < 2 ^ 48 := by
  have c11 := hok.2.2.2.2.2.2.2.2.2.2.1
  have c12 := hok.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt : ∀ x ∈ w.fl.allIds, x.toNat < w.C.hwm := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact c12 x h
    · exact c11 _ (Or.inr (List.mem_map.2 ⟨x, h, rfl⟩))
  have hnd' : (w.fl.allIds.map BitVec.toNat).Nodup :=
    List.Pairwise.map BitVec.toNat (fun a b hab h => hab (BitVec.eq_of_toNat_eq h)) hwf.1
  have hsub : w.fl.allIds.map BitVec.toNat ⊆ List.range w.C.hwm := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact List.mem_range.2 (hlt x hx)
  have := (List.subperm_of_subset hnd' hsub).length_le
  simp only [List.length_map, List.length_range] at this
  omega

end pure

end bbolt
end EtcdGrove
end Perennial
