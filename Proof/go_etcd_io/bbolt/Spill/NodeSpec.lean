/-
`node.spill` (U9e, `notes/bbolt-proof-plan.md`): its spec, unit-internal (its callers are
`Bucket.spill` and itself). Over the writer's records `X` and its database side `w`, with the
spill's global state (`spG`); the node is spilled already (a piece: it returns at once), or it is
the top of an unspilled tree (`uTree`): a child of a node with a page (the child case: its
pieces put in the parent's entries, the parent's children grown by them) or a node without a
parent (the top case: the bucket's root node, or a root a split made; the new root, after
spilling the roots splits make, written).

The slots: `O` the slots owned outside the tree (the other trees being spilled, the kept ones),
`D` the tree's; `slotInv` of both before and of `O` and the pieces' after, so allocations never
take an owned slot, the tree's slots are kept or pending, and the pieces' are the tree's or new.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section pieces
variable [GooseExts]

/-- **A piece of a spilled node**: its node, page id, first key and pages. -/
structure Piece where
  l : Loc
  id : w64
  k : List w8
  S : List Nat

/-- The first key of piece `i` (empty past the end). -/
def pcKey (ps : List Piece) (i : Nat) : List w8 := ((ps[i]?).map Piece.k).getD []

/-- The entry `parent.put(key, k, nil, id, 0)` leaves for a piece, by data. -/
def pcDat (x : Piece) : w32 × w64 × List w8 × List w8 := (W32 0, x.id, x.k, [])

/-- The slots of the pieces. -/
def pcSlots (P : Pages) (ps : List Piece) : List Nat := ps.flatMap fun x => pgSlots P x.S

/-- **The pieces `ps` of a node spilled in bucket `bl`** under the parent `pl`, within `[lo, hi)`,
of height `h`: live spilled nodes without children (`n.children = nil`), distinct, each written
at its page, a finished subtree from its first key up to the next piece's (`hi` for the last). -/
def piecesOK (X : WX) (bl pl : Loc) (P : Pages) (hwm : Nat) (lo hi : Option (List w8)) (h : Nat)
    (ps : List Piece) : Prop :=
  ps ≠ [] ∧ (ps.map Piece.l).Nodup ∧
  ∀ i x, ps[i]? = some x → ∃ rl, X.node bl x.l = some rl ∧ x.l ∈ X.live ∧
    rl.nv.bucket' = bl ∧ rl.nv.spilled' = true ∧ rl.cs = [] ∧ rl.nv.parent' = pl ∧
    rl.nv.pgid' = x.id ∧ rl.key = x.k ∧ keyIn lo hi x.k ∧
    fTree P hwm x.id.toNat x.k (childHi hi (pcKey ps) ps.length i) h x.S

/-- **The parent `rp'` after its child's spill** (the child's entry `j` replaced by the pieces'
entries, the pieces after the first appended to its children; its struct but the slices, its key
and capacity as before; its sources may have changed). -/
def parentSpilled (rp rp' : NRec) (j : Nat) (ps : List Piece) : Prop :=
  rp'.ws.map wDat = (rp.ws.take j).map wDat ++ ps.map pcDat ++ (rp.ws.drop (j + 1)).map wDat ∧
  rp'.cs = rp.cs ++ (ps.drop 1).map Piece.l ∧
  rp'.nv = { rp.nv with inodes' := rp'.nv.inodes', children' := rp'.nv.children',
                        key' := rp'.nv.key' } ∧
  (rp'.nv.key' = slice.nil ↔ rp.nv.key' = slice.nil) ∧
  rp'.key = rp.key ∧ rp'.capOwn = rp.capOwn ∧ rp'.ins.length = rp'.ws.length

/-- The context of a node's spill: a child (of `pl`, record `rp`, its entry `j`, the parent's
bounds `[plo, phi)`), or a top node. -/
inductive SpCase where
  | child (pl : Loc) (rp : NRec) (j : Nat) (plo phi : Option (List w8))
  | top

/-- **Where the node `n` (record `rn`) of bucket `bl` sits** for its spill, its bounds `[lo, hi)`:
a child of `pl` (record `rp`, with a page, a live unspilled branch within `[plo, phi)`), entry `j`
of it; or a top node (no parent), the root of its bucket's root node's chain. -/
def spCtx (X : WX) (bl n : Loc) (rn : NRec) (lo hi : Option (List w8)) (N : List Loc) :
    SpCase → Prop
  | .child pl rp j plo phi => rn.nv.parent' = pl ∧ pl ≠ null ∧ pl ∉ N ∧ X.node bl pl = some rp ∧
      uNode X bl pl rp plo phi ∧ rp.nv.isLeaf' = false ∧ rp.nv.pgid' ≠ W64 0 ∧ n ∈ rp.cs ∧
      (∃ w, rp.ws[j]? = some w ∧ w.pgid = rn.nv.pgid' ∧ w.key = rn.key) ∧
      lo = childLo plo (wKey rp.ws) j ∧ hi = childHi phi (wKey rp.ws) rp.ws.length j ∧
      rn.nv.key' ≠ slice.nil
  | .top => rn.nv.parent' = null ∧ ∃ B, X.t.bs !! bl = some B ∧ nodeRootIn B B.bv.rootNode' n

end pieces

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A spill's step from `(X, w)` to `(X', w')`** for the slots `O` owned elsewhere (the frame):
the committed state kept, the freelist after free and allocation steps `st` of the writer (pending
pages kept), the base pages kept, the spill's global state kept, the other owned slots still
owned, the page map changed only outside them, and what the other trees' frees need kept. -/
def spStep (X X' : WX) (w w' : WDb) (O : List Nat) (st : List FLStep) : Prop :=
  w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧ X'.v.pages = X.v.pages ∧
  spG X' w.wtxid (mapLen w'.ms) ∧ X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms ∧
  (∀ s ∈ pendSlots w.fl, s ∈ pendSlots w'.fl) ∧
  (∀ x, spP X' !! x ≠ spP X !! x → x ∉ O) ∧
  (∀ F, (∀ id ∈ F, id ∈ O) → spFree X w.fl w.wtxid F → spFree X' w'.fl w.wtxid F)

/-- **`n.spill()`** (see the module doc). The pre: the spill's global state, `n` a node of `bl`,
spilled (a piece), or the top of an unspilled tree (`uTree`, at the spill's page map and mark,
owning `F`, `D`, `N`) in the context `cs` (`spCtx`), the slots owned (`slotInv` of `O ++ D`), its
pages freeable. On success, a spill step (`spStep`) and: for a piece, nothing else; in the child
case, the pieces (`piecesOK`) put in the parent (`parentSpilled`); in the top case, the final root
`rt` (`n`'s root after) written, an `sTree` within `[lo, hi)`; the tree's slots kept by the
pieces (or the root's tree) or pending, theirs the tree's or new, owned with `O`; the untouched
nodes as before (`spFrame`, the touched ones `N`, the parent and fresh nodes). On an error (an
`allocate`'s), the freelist after free and allocation steps, and the mapping intact or lost. -/
abbrev node.spill.spec' : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc) (rn : NRec)
    (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (F D : List Nat) (N : List Loc)
    (cs : SpCase),
  X.node bl n = some rn → spG X w.wtxid (mapLen w.ms) →
  (rn.nv.spilled' = true ∧ rn.nv.bucket' = bl ∧ n ∈ X.live) ∨
  (uTree X bl (spP X) X.t.mv.pgid'.toNat n lo hi h F D N ∧ spCtx X bl n rn lo hi N cs ∧
    slotInv w.fl X.t.mv.pgid'.toNat (O ++ D) ∧ spFree X w.fl w.wtxid F) →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
        wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗ ⌜spStep X X' w w' O st ∧
        ((rn.nv.spilled' = true ∧ X' = X ∧ w' = w) ∨
         (rn.nv.spilled' = false ∧ ∃ T D', spFrame X X' bl (N ++ T) ∧
          (∀ l ∈ T, X.t.objs !! l = none ∨ ∃ pl rp j plo phi, cs = .child pl rp j plo phi ∧ l = pl) ∧
          slotInv w'.fl X'.t.mv.pgid'.toNat (O ++ D') ∧
          (∀ s ∈ D, s ∈ D' ∨ s ∈ pendSlots w'.fl) ∧
          (∀ s ∈ D', s ∈ D ∨ newSlot st X.t.mv.pgid'.toNat s) ∧
          (∀ x, spP X' !! x ≠ spP X !! x → x ∉ D) ∧
          match cs with
          | .child pl rp j _ _ => ∃ ps rp',
              piecesOK X' bl pl (spP X') X'.t.mv.pgid'.toNat lo hi h ps ∧
              (ps.head?.map Piece.l) = some n ∧ D' = pcSlots (spP X') ps ∧
              X'.node bl pl = some rp' ∧ parentSpilled rp rp' j ps ∧ pl ∈ X'.live
          | .top => ∃ rt rr S h', X'.node bl rt = some rr ∧ rt ∈ X'.live ∧
              rr.nv.spilled' = true ∧ rr.nv.parent' = null ∧
              (∃ B', X'.t.bs !! bl = some B' ∧ nodeRootIn B' n rt) ∧
              sTree (spP X') X'.t.mv.pgid'.toNat rr.nv.pgid'.toNat lo hi h' S ∧
              D' = pgSlots (spP X') S))⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
        ⌜w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧ X'.v.pages = X.v.pages⌝ ∗
        ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w'))) }}

end spec

end Spill

end bbolt
end EtcdGrove
end Perennial
