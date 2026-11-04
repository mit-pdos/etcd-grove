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

end step

end Spill

end bbolt
end EtcdGrove
end Perennial
