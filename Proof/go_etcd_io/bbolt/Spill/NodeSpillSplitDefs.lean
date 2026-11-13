/-
`node.spill` after its children's loop (U9m, `notes/bbolt-proof-plan.md`; pure): **the records
after `n.split(pageSize)`** (`splitRel`), what the pieces' loop starts from. From `X1` (after
`n.children = nil`, `n`'s record `rN`) to `X2`: the pieces `xs` (`node.split`'s, `n` first, the
others fresh), their entries `wss` (`n`'s entries cut at the pieces' inode counts), each piece a
live childless node of `bl` under the common parent `pl` (the first keeps `n`'s key, the others
have none); the parent `n`'s (the pieces after the
first appended to its children) or, for a top node split in two or more, a fresh one whose
children are the pieces; nothing else touched.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesKill
public import Proof.go_etcd_io.bbolt.Spill.Split
public import Proof.go_etcd_io.bbolt.Spill.UTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section defs
variable [GooseExts] [GoGlobalContext]

/-- **The record of piece `x`** (entries `ws`) after the split of `n` (record `rN`): `n`'s own
record with the piece's struct, inodes and entries (owning its inodes' capacity only when not
split, `one`), or a fresh node's (no key, no children). -/
def splitRec (rN : NRec) (x : Loc × node × List Inode) (ws : List WEntry) (first one : Bool) :
    NRec :=
  if first then { rN with nv := x.2.1, ins := x.2.2, ws := ws, capOwn := one }
  else ⟨x.2.1, x.2.2, ws, [], [], Src.stale, false⟩

/-- **The new parent's record** of a top node split in two or more (struct `pv`, children `ls`):
no entries yet, owning its (nil) inodes' capacity. -/
def newParRec (pv : node) (ls : List Loc) : NRec := ⟨pv, [], [], ls, [], Src.stale, true⟩

/-- **The records after `n.split(pageSize)`** (see the module doc), but the spill's global state.
`pl` the pieces' parent (`null` for an unsplit top node), `rp` its record before (child case) and
`rp'` after. -/
structure splitRel0 (X1 X2 : WX) (bl n : Loc) (rN : NRec) (xs : List (Loc × node × List Inode))
    (wss : List (List WEntry)) (pl : Loc) (rp' : NRec) : Prop where
  ne : xs ≠ []
  head : (xs.head?.map (·.1)) = some n
  nd : (xs.map (·.1)).Nodup
  len : wss.length = xs.length
  ws : wss.flatten = rN.ws
  ins : (xs.map (·.2.2)).flatten = rN.ins
  plen : ∀ (i : Nat) (x : Loc × node × List Inode) (w : List WEntry), xs[i]? = some x → wss[i]? = some w → w.length = x.2.2.length ∧ (2 ≤ xs.length → 0 < w.length)
  prec : ∀ (i : Nat) (x : Loc × node × List Inode) (w : List WEntry), xs[i]? = some x → wss[i]? = some w →
    X2.node bl x.1 = some (splitRec rN x w (decide (i = 0)) (decide (xs.length = 1))) ∧
    x.1 ∈ X2.live ∧ x.2.1.bucket' = bl ∧ x.2.1.isLeaf' = rN.nv.isLeaf' ∧
    x.2.1.spilled' = false ∧ x.2.1.pgid' = (if i = 0 then rN.nv.pgid' else W64 0) ∧
    x.2.1.parent' = pl ∧ x.2.1.children' = slice.nil ∧
    x.2.1.key' = (if i = 0 then rN.nv.key' else slice.nil)
  fresh : ∀ x ∈ xs.drop 1, X1.t.objs !! x.1 = none
  par : (rN.nv.parent' = null ∧ xs.length = 1 ∧ pl = null) ∨
    (rN.nv.parent' = null ∧ 2 ≤ xs.length ∧ pl ≠ null ∧ X1.t.objs !! pl = none ∧
      rp' = newParRec (newParent rN.nv rp'.nv.children') (xs.map (·.1)) ∧
      X2.node bl pl = some rp' ∧ pl ∈ X2.live) ∨
    (rN.nv.parent' ≠ null ∧ pl = rN.nv.parent' ∧ ∃ rp, X1.node bl pl = some rp ∧
      rp' = { rp with nv := { rp.nv with children' := rp'.nv.children' },
                      cs := rp.cs ++ (xs.drop 1).map (·.1) } ∧
      X2.node bl pl = some rp' ∧ (pl ∈ X2.live ↔ pl ∈ X1.live))
  frame : spFrame X1 X2 bl (xs.map (·.1) ++ [pl])
  same : X2.t.mv = X1.t.mv ∧ X2.t.bufs = X1.t.bufs ∧ X2.t.pm = X1.t.pm ∧ X2.v = X1.v

/-- **The records after `n.split(pageSize)`** (`splitRel0`), and the spill's global state kept
(`G`): for a top node split in two, given that `n` is the root of its bucket's root node (`b.rootNode`
is `n`: the new root `pl` then roots it). -/
structure splitRel (X1 X2 : WX) (bl n : Loc) (rN : NRec) (xs : List (Loc × node × List Inode))
    (wss : List (List WEntry)) (pl : Loc) (rp' : NRec) : Prop
    extends splitRel0 X1 X2 bl n rN xs wss pl rp' where
  G : (rN.nv.parent' = null → 2 ≤ xs.length → ∀ B rt, X1.t.bs !! bl = some B →
      nodeRootIn B B.bv.rootNode' rt → rt = n) →
    ∀ txid ml fl, spG X1 txid ml fl → spG X2 txid ml fl

end defs

end Spill

end bbolt
end EtcdGrove
end Perennial
