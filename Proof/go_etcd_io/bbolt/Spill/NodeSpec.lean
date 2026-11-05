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
of height `h`: live spilled nodes without children (`n.children = nil`), not empty, distinct, each written
at its page, its first key not empty and fitting an entry (U9f: the parent's entry), a finished
subtree from its first key up to the next piece's (`hi` for the last). -/
def piecesOK (X : WX) (bl pl : Loc) (P : Pages) (hwm : Nat) (lo hi : Option (List w8)) (h : Nat)
    (ps : List Piece) : Prop :=
  ps ≠ [] ∧ (ps.map Piece.l).Nodup ∧
  ∀ i x, ps[i]? = some x → ∃ rl, X.node bl x.l = some rl ∧ x.l ∈ X.live ∧
    rl.nv.bucket' = bl ∧ rl.nv.spilled' = true ∧ rl.cs = [] ∧ rl.nv.parent' = pl ∧
    rl.nv.pgid' = x.id ∧ rl.key = x.k ∧ 0 < rl.ws.length ∧ keyIn lo hi x.k ∧
    0 < x.k.length ∧ x.k.length ≤ bboltEntryMax ∧
    fTree P hwm x.id.toNat x.k (childHi hi (pcKey ps) ps.length i) h x.S (treeEls P x.id.toNat)

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

/-- **`x` is on the chain of parents from `a` up to `rt`** (in `B`; `rt` included). -/
inductive onChain (B : BRec) : Loc → Loc → Loc → Prop
  | self (a rt : Loc) : onChain B a rt a
  | up (a rt x : Loc) (r : NRec) : B.ns !! a = some r → a ≠ rt → onChain B r.nv.parent' rt x →
      onChain B a rt x

/-- **Where the node `n` (record `rn`) of bucket `bl` sits** for its spill, its bounds `[lo, hi)`:
a child of `pl` (record `rp`, with a page, a live unspilled branch within `[plo, phi)`), entry `j`
of it, its children nodes of its tree (U9j: no earlier spill's pieces, so that their kill is
framed), not empty (U9w: `node.spill` reads a piece's first inode under a parent); or a top
node (no parent), the root of its bucket's root node's chain, the chain's other nodes spilled
(U9z; U9w4: records only, not live: a new root's own spill, `node.spill`'s recursion, follows the
kill of its children, the pieces, among them the previous top node, on the chain). -/
def spCtx (X : WX) (bl n : Loc) (rn : NRec) (lo hi : Option (List w8)) (N : List Loc) :
    SpCase → Prop
  | .child pl rp j plo phi => rn.nv.parent' = pl ∧ pl ≠ null ∧ pl ∉ N ∧ X.node bl pl = some rp ∧
      uNode X bl pl rp plo phi ∧ rp.nv.isLeaf' = false ∧ rp.nv.pgid' ≠ W64 0 ∧ n ∈ rp.cs ∧
      (∃ w, rp.ws[j]? = some w ∧ w.pgid = rn.nv.pgid' ∧ w.key = rn.key) ∧
      lo = childLo plo (wKey rp.ws) j ∧ hi = childHi phi (wKey rp.ws) rp.ws.length j ∧
      rn.nv.key' ≠ slice.nil ∧ (∀ c ∈ rn.cs, c ∈ N) ∧ 0 < rn.ws.length
  | .top => rn.nv.parent' = null ∧ ∃ B, X.t.bs !! bl = some B ∧ nodeRootIn B B.bv.rootNode' n ∧
      ∀ x, onChain B B.bv.rootNode' n x → x ≠ n → ∃ rx, X.node bl x = some rx ∧ rx.nv.spilled' = true

/-- **The writer's buffers are dirty pages of fresh slots** (`spillBufs`' per-buffer clause,
`Commit`'s `tx.write` premises): each buffer's header names its id, its length is its extent's,
its extent lies in `[2, mark)`, and its slots are no tree slots of the committed state `C`, not
pending in `fl`, (maintainer 12, item 4) not free in `fl`, and in no other buffer's extent (the
extents pairwise disjoint: `tx.write`'s slots without repeats). (U9x's, moved here by U9w2: a
spill step keeps it, `spStep`.) -/
def bufsOK (X : WX) (C : CommitSt) (fl : FLPg) : Prop :=
  ∀ id pg, X.t.bufs !! id = some pg → pageId pg = id.toNat ∧
    pg.length = 4096 * (1 + pageOverflow pg) ∧ 2 ≤ id.toNat ∧
    id.toNat + (1 + pageOverflow pg) ≤ X.t.mv.pgid'.toNat ∧
    ∀ j < 1 + pageOverflow pg, id.toNat + j ∉ treeSlots C ∧ id.toNat + j ∉ pendSlots fl ∧
      (∀ x ∈ fl.free, x.toNat ≠ id.toNat + j) ∧
      ∀ id' pg', X.t.bufs !! id' = some pg' → ∀ j' < 1 + pageOverflow pg',
        id.toNat + j = id'.toNat + j' → id' = id

/-- **The buffers grow and cover the mark's growth** (D-K, U9w6: for `Bucket.spill`'s `markCov`):
every buffer of `X` is one of `X'`, and every slot from `X`'s mark to `X'`'s lies in a buffer's
extent of `X'` (the mark moves only by `allocate`'s mark case, which adds the run as a buffer). -/
def markGrow (X X' : WX) : Prop :=
  (∀ id pg, X.t.bufs !! id = some pg → X'.t.bufs !! id = some pg) ∧
  ∀ s, X.t.mv.pgid'.toNat ≤ s → s < X'.t.mv.pgid'.toNat →
    ∃ id pg, X'.t.bufs !! id = some pg ∧ id.toNat ≤ s ∧ s < id.toNat + (1 + pageOverflow pg)

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
owned, the page map changed only outside them and outside the pending slots (U9h: a slot one
child's spill freed keeps its page through its siblings' spills), what the other trees' frees
need kept, and (coordinator's decision, for `Bucket.spill`'s `RInv.bufs`) the buffers dirty pages
of fresh slots (`bufsOK`: every new buffer an allocation written with its header and length below
the new mark, on no tree slot of `w.C`; no buffer slot made pending: the spill frees only base
pages); (U9w6, D-K) the buffers grown over the mark's growth (`markGrow`). -/
def spStep (X X' : WX) (w w' : WDb) (O : List Nat) (st : List FLStep) : Prop :=
  w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧ X'.v.pages = X.v.pages ∧
  spG X' w.wtxid (mapLen w'.ms) w'.fl ∧ X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms ∧
  (∀ s ∈ pendSlots w.fl, s ∈ pendSlots w'.fl) ∧
  (∀ x, spP X' !! x ≠ spP X !! x → x ∉ O ∧ x ∉ pendSlots w.fl) ∧
  (∀ F, (∀ id ∈ F, id ∈ O) → spFree X w.fl w.wtxid F → spFree X' w'.fl w.wtxid F) ∧
  (bufsOK X w.C w.fl → bufsOK X' w.C w'.fl) ∧ markGrow X X'

/-- **`n.spill()`'s pre** (pure): `n` a node of `bl` (record `rn`), the spill's global state, and
`n` spilled (a piece) or the top of an unspilled tree in the context `cs`, its slots owned with
`O`, its pages freeable, the view the committed tree's, the free ids no tree slot and the tree's
slots below the mark (coordinator: for `spStep`'s `bufsOK`), and (U9w3, for the kill of `n`'s
children) the bucket's parent pointers (`parOK`). -/
def spPre (X : WX) (w : WDb) (bl n : Loc) (rn : NRec) (O : List Nat) (lo hi : Option (List w8))
    (h : Nat) (F D : List Nat) (N : List Loc) (E : List El) (cs : SpCase) : Prop :=
  X.node bl n = some rn ∧ spG X w.wtxid (mapLen w.ms) w.fl ∧
  ((rn.nv.spilled' = true ∧ rn.nv.bucket' = bl ∧ n ∈ X.live) ∨
   (uTree X bl (spP X) X.t.mv.pgid'.toNat n lo hi h F D N E ∧ spCtx X bl n rn lo hi N cs ∧
    slotInv w.fl X.t.mv.pgid'.toNat (O ++ D) ∧ spFree X w.fl w.wtxid F ∧
    X.v = View.ofC X.v.base w.C ∧
    (∀ y ∈ w.fl.free, ¬ coversSlot w.C.pages y.toNat) ∧ (∀ s ∈ treeSlots w.C, s < X.t.mv.pgid'.toNat) ∧
    parOK X bl))

/-- **`n.spill()`'s success** (pure), from `(X, w)` to `(X', w')` by the steps `st` (see
`node.spill.spec'`; U9w3: an unspilled node's spill keeps the bucket's parent pointers). -/
def spDone (X X' : WX) (w w' : WDb) (bl n : Loc) (rn : NRec) (O : List Nat)
    (lo hi : Option (List w8)) (h : Nat) (D : List Nat) (N : List Loc) (E : List El)
    (cs : SpCase) (st : List FLStep) : Prop :=
  spStep X X' w w' O st ∧
  ((rn.nv.spilled' = true ∧ X' = X ∧ w' = w) ∨
   (rn.nv.spilled' = false ∧ ∃ T D', spFrame X X' bl (N ++ T) ∧
    (∀ l ∈ T, X.t.objs !! l = none ∨ (∃ pl rp j plo phi, cs = .child pl rp j plo phi ∧ l = pl) ∨
      (cs = .top ∧ l ∈ rn.cs ∧ ∀ r, X.node bl l = some r → ∃ r', X'.node bl l = some r' ∧
        nodeSim r r')) ∧
    slotInv w'.fl X'.t.mv.pgid'.toNat (O ++ D') ∧
    (∀ s ∈ D, s ∈ D' ∨ s ∈ pendSlots w'.fl) ∧
    (∀ s ∈ D', s ∈ D ∨ newSlot st X.t.mv.pgid'.toNat s) ∧
    (∀ x, spP X' !! x ≠ spP X !! x → x ∉ D) ∧ parOK X' bl ∧
    match cs with
    | .child pl rp j _ _ => ∃ ps rp',
        piecesOK X' bl pl (spP X') X'.t.mv.pgid'.toNat lo hi h ps ∧
        (ps.head?.map Piece.l) = some n ∧ (∀ x ∈ ps.drop 1, X.t.objs !! x.l = none) ∧
        D' = pcSlots (spP X') ps ∧ ps.flatMap (fun x => treeEls (spP X') x.id.toNat) = E ∧
        X'.node bl pl = some rp' ∧ parentSpilled rp rp' j ps ∧ pl ∈ X'.live
    | .top => ∃ rt rr S h', X'.node bl rt = some rr ∧ rt ∈ X'.live ∧
        rr.nv.spilled' = true ∧ rr.nv.parent' = null ∧
        (∃ B', X'.t.bs !! bl = some B' ∧ nodeRootIn B' n rt) ∧
        sTree (spP X') X'.t.mv.pgid'.toNat rr.nv.pgid'.toNat lo hi h' S ∧
        D' = pgSlots (spP X') S ∧ treeEls (spP X') rr.nv.pgid'.toNat = E))

/-- **A spill's error facts** from `(X, w)` to `(X', w')` by the steps `st`: the committed state
kept, the freelist after free and allocation steps, the base pages kept, and (U9w3, for
`Bucket.spill`'s error post) the transaction's record and root kept, the root bucket kept, the
meta kept but its mark. -/
def spErr (X X' : WX) (w w' : WDb) (st : List FLStep) : Prop :=
  w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧ X'.v.pages = X.v.pages ∧
  X'.t.t = X.t.t ∧ X'.rl = X.rl ∧ ((X.t.bs !! X.rl).isSome → (X'.t.bs !! X'.rl).isSome) ∧
  X'.t.mv = { X.t.mv with pgid' := X'.t.mv.pgid' }

/-- **`n.spill()`'s post**: on success `spDone`, on an error `spErr` (the freelist after free and
allocation steps, the base pages, the transaction's record, root and meta but its mark kept), the
mapping intact or lost. -/
def spPost (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc)
    (rn : NRec) (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (D : List Nat)
    (N : List Loc) (E : List El) (cs : SpCase) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
      wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗ ⌜spDone X X' w w' bl n rn O lo hi h D N E cs st⌝) ∨
    (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
      ⌜spErr X X' w w' st⌝ ∗
      ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w'))))

/-- **`n.spill()`** (see the module doc). The pre: the spill's global state, `n` a node of `bl`,
spilled (a piece), or the top of an unspilled tree (`uTree`, at the spill's page map and mark,
owning `F`, `D`, `N`, its leaf elements `E`) in the context `cs` (`spCtx`), the slots owned (`slotInv` of `O ++ D`), its
pages freeable. On success, a spill step (`spStep`) and: for a piece, nothing else; in the child
case, the pieces (`piecesOK`) put in the parent (`parentSpilled`), their trees' leaf elements
`E` in order; in the top case, the final root `rt` (`n`'s root after) written, an `sTree` within
`[lo, hi)` whose leaf elements are `E`; the tree's slots kept by the
pieces (or the root's tree) or pending, theirs the tree's or new, owned with `O`; the untouched
nodes as before (`spFrame`, the touched ones `N`, the parent and fresh nodes, and in the top
case `n`'s children at the start, killed: U9j, the recursion on a new root whose children are
the pieces). On an error (an
`allocate`'s), the freelist after free and allocation steps, and the mapping intact or lost. -/
abbrev node.spill.spec' : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc) (rn : NRec)
    (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (F D : List Nat) (N : List Loc)
    (E : List El) (cs : SpCase),
  spPre X w bl n rn O lo hi h F D N E cs →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err; spPost K tx r m X w bl n rn O lo hi h D N E cs err }}

omit package_sem in
/-- The writer's view is the committed tree's (`wdbW`'s pure fact; `spPre`'s last clause). -/
theorem wdbW_ofC (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ wdbW K tx v w ∗ ⌜v = View.ofC v.base w.C⌝ := by
  unfold wdbW
  iintro ⟨H, %Hp⟩
  isplitl [H]
  · isplitl [H]
    · iexact H
    · ipureintro; exact Hp
  · ipureintro; exact Hp.2.2

end spec

end Spill

end bbolt
end EtcdGrove
end Perennial
