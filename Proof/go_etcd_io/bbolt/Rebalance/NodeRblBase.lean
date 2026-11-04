/-
Pure facts `node.rebalance`'s WP proof uses (U8b, `notes/bbolt-proof-plan.md`): the search index
of an entry's own key in sorted entries (`node.del` of a child's key), the writer's txid from
the invariant and the database side, and the size bound `node.size`'s spec takes.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.HeapRbl
public import Proof.go_etcd_io.bbolt.Write.NodeEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- In sorted entries, an entry's key searches to its index. -/
theorem wsIdx_at (ws : List WEntry) (i : Nat) (w : WEntry) (hs : wsSorted ws)
    (hw : ws[i]? = some w) : wsIdx ws w.key = i := by
  have hi := (List.getElem?_eq_some_iff.1 hw).1
  have hk : wKey ws i = w.key := by unfold wKey; rw [hw]; rfl
  apply Write.wsIdx_of_bounds ws w.key i (by omega)
  · intro k hk'
    rw [← hk]; exact hs k i hk' hi
  · intro _; rw [hk]; exact go.goStringLt_irrefl _

/-- `del` of an entry's own key in sorted entries: found, and the entry removed. -/
theorem wsDelAt_at (ws : List WEntry) (i : Nat) (w : WEntry) (hs : wsSorted ws)
    (hw : ws[i]? = some w) : wsFound ws w.key ∧ wsDelAt ws w.key = ws.eraseIdx i := by
  have hidx := wsIdx_at ws i w hs hw
  have hf : wsFound ws w.key := by
    unfold wsFound; rw [hidx, hw]; rfl
  refine ⟨hf, ?_⟩
  unfold wsDelAt
  rw [if_pos hf, hidx, List.eraseIdx_eq_take_drop_succ]

/-- **A node's page size fits an `int`** (`node.size`'s premise). A `sorry`: nothing in `rblX`
bounds a node's number of entries or their sizes (see the U8b report). -/
theorem rblX_insSize (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) (bl : Loc) (B : BRec)
    (n : Loc) (r : NRec) (hI : rblX X fl dbl dfc) (hb : X.t.bs !! bl = some B)
    (hr : B.ns !! n = some r) : insSize r.ins < 2 ^ 63 := by
  sorry

/-- The writer's txid (`tx.meta.txid`) is the database side's `wtxid`. -/
theorem rblX_wtxid (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) (w : WDb)
    (hI : rblX X fl dbl dfc) (hv : X.v = View.ofC X.v.base w.C) : X.t.mv.txid' = w.wtxid := by
  have h := hI.1.2.2.2.1
  have hv' : X.v.txid = w.C.txid := by rw [hv]; rfl
  unfold WDb.wtxid
  apply BitVec.eq_of_toNat_eq
  rw [← h, hv']
  have hlt : w.C.txid + 1 < 2 ^ 64 := by
    have := X.t.mv.txid'.isLt; rw [← h, hv'] at this; exact this
  simp only [BitVec.toNat_ofInt]
  omega

end pure

end bbolt
end EtcdGrove
end Perennial
