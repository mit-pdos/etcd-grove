/-
`node.spill` after its children's loop (U9s, `notes/bbolt-proof-plan.md`; pure): **one piece's
premises** (`pcPre`), the pure premises of `Spill/NodeSpillPiecesOne`'s `pieceOne_wp` for the
piece `l` (record `rl`) at `(X, w)`, as one proposition, what the pieces' loop's invariant gives
at each iteration (`Spill/NodeSpillTailWp`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesStep
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesDefs
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section defs
variable [GooseExts]

/-- **The inodes' slices have their entries' lengths** (what `wOwn` gives of a live node's
entries: `node.size` reads the slices' lengths, the bounds are on the entries'). -/
def insLens (ins : List Inode) (ws : List WEntry) : Prop :=
  ∀ (k : Nat) (it : Inode) (w : WEntry), ins[k]? = some it → ws[k]? = some w →
    it.key'.len.toNat = w.key.length ∧ it.value'.len.toNat = w.value.length

/-- **The pure premises of `pieceOne_wp`** for the piece `l` (record `rl`) at `(X, w)` (see the
module doc), in its order: `hlv`, `hbl`, `hfree`, `hG`, `hne`, `hil`, `hsz`, `hfit`, `hn16`,
`hbody`, `hid`, `hpar`, `hsz31` (coordinator: the size an `int`; U9w: `hne` only with a parent, an empty root leaf is written). -/
def pcPre (X : WX) (w : WDb) (bl l : Loc) (rl : NRec) : Prop :=
  l ∈ X.live ∧ rl.nv.bucket' = bl ∧
  (rl.nv.pgid' ≠ W64 0 → X.t.pm !! rl.nv.pgid' = none ∧ X.t.mv.txid' = w.wtxid ∧
    ∃ pg, X.v.pages !! rl.nv.pgid'.toNat = some pg ∧
      16 ≤ pg.length ∧ pageId pg = rl.nv.pgid'.toNat ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
      w.fl.canFree w.wtxid rl.nv.pgid' (1 + pageOverflow pg)) ∧
  (∀ X1 w1 st, pcFreed X w bl l rl X1 w1 st → spG X1 w.wtxid (mapLen w1.ms) w1.fl) ∧
  (rl.nv.parent' ≠ null → 0 < rl.ws.length) ∧ rl.ins.length = rl.ws.length ∧
  insSize rl.ins + 4096 < 2 ^ 62 ∧ pageFits (wsMs rl.ws) ∧ rl.ws.length < 0xFFFF ∧
  16 + (pageBody true (wsMs rl.ws)).length ≤ pcCount (insSize rl.ins) * 4096 ∧
  (∀ X1 w1 st X2 fl2 p id, pcFreed X w bl l rl X1 w1 st →
    allocRes X1 X2 w1.fl fl2 w.wtxid (pcCount (insSize rl.ins)) p id →
    id.toNat < X2.t.mv.pgid'.toNat ∧ (rl.nv.isLeaf' = false → ∀ e ∈ rl.ws, e.pgid ≠ id)) ∧
  (rl.nv.parent' ≠ null → ∃ rp, X.node bl rl.nv.parent' = some rp ∧
    rl.nv.parent' ∈ X.live ∧ rl.nv.parent' ≠ l ∧ rp.capOwn = true ∧ wsSorted rp.ws) ∧
  insSize rl.ins < 2 ^ 31 - 1

end defs

end Spill

end bbolt
end EtcdGrove
end Perennial
