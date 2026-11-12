/-
`node.spill` after its children's loop (U9u, `notes/bbolt-proof-plan.md`; pure): **an
allocation's id is below the new mark** (`allocRes_id_lt`, `pieceOne_wp`'s `hid`, its first part):
from the free ids (all below the mark, `slotInv`'s last clause) or at the mark.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section alloc
variable [GooseExts] [GoGlobalContext]

theorem addPage_pgid (X : WX) (id : w64) (p : Loc) (count : Nat) (hwm : w64) :
    (X.addPage id p count hwm).t.mv.pgid' = hwm := rfl

/-- **An allocation's id is below the new mark** (see the module doc). -/
theorem allocRes_id_lt {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc}
    {id : w64} (h : allocRes X X' fl fl' txid count p id)
    (hfree : ∀ x ∈ fl.allIds, x.toNat < X.t.mv.pgid'.toNat) :
    id.toNat < X'.t.mv.pgid'.toNat := by
  obtain ⟨hc, -, Xr, -, hX'⟩ := h
  rcases hX' with ⟨⟨-, hrun⟩, -, rfl⟩ | ⟨rfl, -, hlt, rfl⟩
  · rw [addPage_pgid]
    exact hfree id (List.mem_append_left _ (hrun id ⟨Nat.le_refl _, by omega⟩))
  · rw [addPage_pgid]
    have : (X.t.mv.pgid' + W64 (count : Int)).toNat = X.t.mv.pgid'.toNat + count := by word
    rw [this]; omega

/-- The same from the slots' invariant. -/
theorem allocRes_id_lt' {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc}
    {id : w64} {L : List Nat} (h : allocRes X X' fl fl' txid count p id)
    (hs : slotInv fl X.t.mv.pgid'.toNat L) : id.toNat < X'.t.mv.pgid'.toNat :=
  allocRes_id_lt h hs.2.2.2

end alloc

end Spill

end bbolt
end EtcdGrove
end Perennial
