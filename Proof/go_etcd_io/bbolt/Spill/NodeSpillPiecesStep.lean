/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`; pure): **one piece's
step on the records** (what `Spill/NodeSpillPiecesOne`'s `pieceOne_wp` leaves): the allocated
buffer holding the written page (`WX.setBuf`, `pcPage`), the piece's record written and spilled,
its key its first entry's when it has a parent (`pcRec`), and the parent's entries with the
piece's (`pcPar`: `node.put(key, inodes[0].Key(), nil, pgid, 0)`, `key` the piece's key or, nil,
its first key).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.PageBuf
public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section model
variable [GooseExts]

/-- `X` with the buffer `id` holding `bs`. -/
def WX.setBuf (X : WX) (id : w64) (bs : List w8) : WX :=
  { X with t := { X.t with bufs := X.t.bufs.insert id bs } }

/-- A record's first entry (its first inode's key: `inodes[0].Key()`). -/
def NRec.w0 (r : NRec) : WEntry := r.ws.headD default

/-- A record's first inode's key slice. -/
def NRec.k0 (r : NRec) : GoSlice := ((r.ins.head?).map Inode.key').getD slice.nil

theorem WX.setNode_node_same {X : WX} {bl l : Loc} {r : NRec} (hn : X.node bl l = some r)
    (r' : NRec) : (X.setNode bl l r').node bl l = some r' := by
  unfold WX.node at hn ⊢
  unfold WX.setNode
  cases e : X.t.bs !! bl with
  | none => rw [e] at hn; cases hn
  | some B => simp [WX.setBkt]

theorem WX.setNode_node_ne {X : WX} {bl l l' : Loc} (bl' : Loc) (r' : NRec) (h : l' ≠ l) :
    (X.setNode bl l r').node bl' l' = X.node bl' l' := by
  unfold WX.node WX.setNode
  cases e : X.t.bs !! bl with
  | none => rfl
  | some B =>
    simp only [WX.setBkt]
    by_cases hb : bl = bl'
    · subst hb; simp [e]; intro h'; exact absurd h'.symm h
    · simp [hb]

theorem WX.setNode_live (X : WX) (bl l : Loc) (r' : NRec) : (X.setNode bl l r').live = X.live := by
  unfold WX.setNode; split <;> rfl

theorem WX.setNode_v (X : WX) (bl l : Loc) (r' : NRec) : (X.setNode bl l r').v = X.v := by
  unfold WX.setNode; split <;> rfl

end model

namespace Spill

section step
variable [GooseExts]

/-- The pages a piece of `insSize` `sz` takes (`(size + pageSize - 1) / pageSize`). -/
def pcCount (sz : Nat) : Nat := (sz + 4095) / 4096

/-- **The page `node.write` leaves** in a buffer of `count` pages allocated at `id`, for a node of
kind `leaf` with entries `ws`. -/
def pcPage (id : w64) (leaf : Bool) (ws : List WEntry) (count : Nat) : List w8 :=
  wPage id leaf (wsMs ws) (W32 ((count - 1 : Nat) : Int))
    (List.replicate (count * 4096 - 16 - (pageBody leaf (wsMs ws)).length) (W8 0))

/-- **The key a piece is put under** in its parent: its key, or (nil) its first key. -/
def pcOldKey (r : NRec) : List w8 := if r.nv.key' = slice.nil then r.w0.key else r.key

/-- **The entry a piece leaves in its parent** (`put(…, inodes[0].Key(), nil, pgid, 0)`). -/
def pcEnt (r : NRec) (id : w64) : WEntry :=
  ⟨W32 0, id, r.w0.key, [], r.w0.ks, Src.own DFrac.discard⟩

/-- **A piece's record after its write** at the page `id`: spilled, its key (with a parent,
`hp`) its first inode's. -/
def pcRec (r : NRec) (id : w64) (hp : Bool) : NRec :=
  if hp then
    { r with nv := { r.nv with pgid' := id, spilled' := true,
                               key' := r.k0 },
             key := r.w0.key, ksrc := r.w0.ks }
  else { r with nv := { r.nv with pgid' := id, spilled' := true } }

/-- **The parent's record after the piece's put** (the inodes slice `s`, the inodes `ins`). -/
def pcPar (rp r : NRec) (id : w64) (s : GoSlice) (ins : List Inode) : NRec :=
  rp.withEnts s ins (wsPutAt rp.ws (pcOldKey r) (pcEnt r id))

/-- **A piece's inline free** (`pieceFree_wp`'s post): nothing (no page), or its page freed for
the writer and its page id `0`; the freelist steps `st`. -/
def pcFreed (X : WX) (w : WDb) (bl l : Loc) (r : NRec) (X1 : WX) (w1 : WDb) (st : List FLStep) :
    Prop :=
  (r.nv.pgid' = W64 0 ∧ X1 = X ∧ w1 = w ∧ st = []) ∨
  (∃ pg, r.nv.pgid' ≠ W64 0 ∧ X.v.pages !! r.nv.pgid'.toNat = some pg ∧
    X1 = X.setNode bl l { r with nv := { r.nv with pgid' := W64 0 } } ∧
    w1 = w.withFl (w.fl.freePages w.wtxid r.nv.pgid' (1 + pageOverflow pg)) ∧
    st = [FLStep.free r.nv.pgid' (1 + pageOverflow pg)])

/-- **The records after a piece's write** (from `X2`, after `allocate`; the piece `l` with record
`ra`, its parent `pl` with record `rp`, if it has one: `hp`): the piece written (`pcRec`), the
parent with its entry (`pcPar`, the put's slice `s` and inodes `ins`), the buffer the page. -/
def pcFin (X2 : WX) (bl l : Loc) (ra : NRec) (pl : Loc) (rp : NRec) (s : GoSlice)
    (ins : List Inode) (id : w64) (count : Nat) (hp : Bool) : WX :=
  (if hp then (X2.setNode bl l (pcRec ra id true)).setNode bl pl (pcPar rp ra id s ins)
   else X2.setNode bl l (pcRec ra id false)).setBuf id (pcPage id ra.nv.isLeaf' ra.ws count)

/-- **A piece's step** from `(X, w)` (record `r`) to `(X3, w2)`: its free (steps `st`), an
allocation of `count` pages at `id` (from `X1` to `X2`, `ra` the piece's record there, `rp` its
parent's), the records after the write (`pcFin`). -/
def pcStep (X : WX) (w : WDb) (bl l : Loc) (r : NRec) (count : Nat) (X3 : WX) (w2 : WDb)
    (st : List FLStep) (id : w64) : Prop :=
  ∃ X1 w1 X2 p ra rp s ins stf sta, pcFreed X w bl l r X1 w1 stf ∧ st = stf ++ sta ∧
    allocRes X1 X2 w1.fl w2.fl w.wtxid count p id ∧ w2.fl = w1.fl.applySteps w.wtxid sta ∧
    w2.C = w1.C ∧
    X2.t.mv.pgid'.toNat * 4096 ≤ mapLen w2.ms ∧ (w2 = w1.withFl w2.fl ∨ wdbRemap w1 w2) ∧
    X2.node bl l = some ra ∧
    (r.nv.parent' ≠ null → X2.node bl r.nv.parent' = some rp ∧
      ins.length = (wsPutAt rp.ws (pcOldKey ra) (pcEnt ra id)).length ∧ ra.k0 ≠ slice.nil) ∧
    X3 = pcFin X2 bl l ra r.nv.parent' rp s ins id count (decide (r.nv.parent' ≠ null))

end step

end Spill

end bbolt
end EtcdGrove
end Perennial
