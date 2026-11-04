/-
`Commit`'s pure steps (U10g of `notes/bbolt-proof-plan.md`): from one callee's post to the next
callee's premises.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX

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

end pure

end bbolt
end EtcdGrove
end Perennial
