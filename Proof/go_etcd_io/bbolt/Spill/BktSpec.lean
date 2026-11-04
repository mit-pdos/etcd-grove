/-
`Bucket.spill` (U9g, `notes/bbolt-proof-plan.md`): the unit-internal spec of a **nested bucket's
spill** (`child.spill()` in the root bucket's loop), and the vocabulary of `Bucket.spill`'s proof.

Nesting is at most two levels (`rootShape`: the root bucket's leaves hold only bucket entries, a
nested bucket's leaves none), so the recursion `child.spill()` is one level deep: a nested bucket
caches no child bucket (`B.bm = ∅`), its loop runs no iteration, and its spill is its root node's
(`node.spill.spec'`, top case), then `b.rootNode = b.rootNode.root()` and `SetRootPage`. The root
bucket's spill (the frozen `Bucket.spill.spec`) calls this spec for its non-inlineable children.

The pre is `node.spill.spec'`'s for the top case at the bucket's root node (`uTree` from its
logical tree, built by the caller); the post adds to its success the bucket's new root node and
header (`bkRooted`), and the data of the written tree (`treeEntries`, `plainTree`): what the parent's
entry for it needs (`bvalS`, `treeData_spill`'s `hbkts`, `rootShape`'s nested clause).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpec
public import Proof.go_etcd_io.bbolt.Model.TreeData

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section defs
variable [GooseExts]

/-- **A nested bucket's tree holds plain entries** (`rootShape`'s nested clause): every element
of its leaves a plain key/value, its key not empty, within `bboltEntryMax`. -/
def plainTree (P : Pages) (root : Nat) : Prop :=
  ∀ pg ∈ treeLeaves P root, ∀ j < pageCount pg,
    leafFlags pg j % 2 = 0 ∧ 0 < leafKsize pg j ∧ leafKsize pg j + leafVsize pg j ≤ bboltEntryMax

/-- **Plain leaf elements** (by data): flags of a plain entry, key not empty, the entry within
`bboltEntryMax` (a nested bucket's entries, `leafShape`, `entriesBounded`). -/
def plainEls (E : List El) : Prop :=
  ∀ e ∈ E, e.1 % 2 = 0 ∧ 0 < e.2.1.length ∧ e.2.1.length + e.2.2.length ≤ bboltEntryMax

/-- **The bucket record after `b.rootNode = b.rootNode.root(); b.SetRootPage(pgid)`**. -/
def bkRooted (B : BRec) (rt : Loc) (pgid : w64) : BRec :=
  { B with bv := { B.bv with rootNode' := rt }, ib := { B.ib with root' := pgid } }

/-- **A nested bucket's spill's pre** (pure): the bucket `bl` (record `B`) live, caching no
child bucket, the spill's global state; its root node nil, or (`node.spill.spec'`'s top case
at it) the top of an unspilled tree within `(-∞, ∞)` of height `h`, owning `F`, `D`, `N`, its
slots owned with `O`, its pages freeable, its leaf elements `E` plain (`plainEls`) and, as
key/value pairs, the bucket's entries (`lbktEnts`), its nodes' parent pointers (`parOK`, U9w3's
`spPre` clause); (coordinator, U9x3, for `spPre`'s slot facts)
the committed tree's slots below the mark (the root loop's `rinv_treeLt`). -/
def bkPre (X : WX) (w : WDb) (bl : Loc) (B : BRec) (O : List Nat) (h : Nat) (F D : List Nat)
    (N : List Loc) : Prop :=
  X.t.bs !! bl = some B ∧ bl ∈ X.liveB ∧ B.bm = ∅ ∧ spG X w.wtxid (mapLen w.ms) w.fl ∧
  (∀ s ∈ treeSlots w.C, s < X.t.mv.pgid'.toNat) ∧
  (B.bv.rootNode' = null ∨
   ∃ rn E, X.node bl B.bv.rootNode' = some rn ∧ rn.nv.parent' = null ∧
     uTree X bl (spP X) X.t.mv.pgid'.toNat B.bv.rootNode' none none h F D N E ∧
     slotInv w.fl X.t.mv.pgid'.toNat (O ++ D) ∧ spFree X w.fl w.wtxid F ∧
     E.map (fun e => (e.2.1, e.2.2)) = lbktEnts X bl ∧ plainEls E ∧ parOK X bl)

/-- **A nested bucket's spill's success** (pure), from `(X, w)` to `(X', w')` by the steps `st`: a
spill step (`spStep`); if its root node was nil, nothing changed; else, after `node.spill`
(from `X` to `X1`, the frame `spFrame` of the touched nodes `T`), its root node is the final root
`rt` (record `rr`, spilled, no parent) and its header's root `rr`'s page (`bkRooted`), the tree
written there an `sTree` with the slots `D'` (the tree's slots kept or pending, the new ones the
tree's or new, owned with `O`), holding the bucket's plain entries in order (`lbktEnts`). -/
def bkDone (X X' : WX) (w w' : WDb) (bl : Loc) (B : BRec) (O D : List Nat) (st : List FLStep) :
    Prop :=
  spStep X X' w w' O st ∧
  ((B.bv.rootNode' = null ∧ X' = X ∧ w' = w) ∨
   (B.bv.rootNode' ≠ null ∧ ∃ (X1 : WX) (T : List Loc) (B1 : BRec) (rt : Loc) (rr : NRec)
      (S D' : List Nat) (h' : Nat),
    spFrame X X1 bl T ∧ X1.t.bs !! bl = some B1 ∧ B1.ns !! rt = some rr ∧ rt ∈ X1.live ∧
    rr.nv.spilled' = true ∧ rr.nv.parent' = null ∧ X' = X1.setBkt bl (bkRooted B1 rt rr.nv.pgid') ∧
    sTree (spP X') X'.t.mv.pgid'.toNat rr.nv.pgid'.toNat none none h' S ∧
    D' = pgSlots (spP X') S ∧ slotInv w'.fl X'.t.mv.pgid'.toNat (O ++ D') ∧
    (∀ s ∈ D, s ∈ D' ∨ s ∈ pendSlots w'.fl) ∧
    (∀ s ∈ D', s ∈ D ∨ newSlot st X.t.mv.pgid'.toNat s) ∧
    treeEntries (spP X') rr.nv.pgid'.toNat = lbktEnts X bl ∧ plainTree (spP X') rr.nv.pgid'.toNat))

section spec
variable [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A nested bucket's spill's post**: on success `bkDone`, on an error (an `allocate`'s)
`spErr` (the freelist after free and allocation steps, the base pages, the transaction's record,
root and meta but its mark kept), the mapping intact or lost. -/
def bkPost (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec)
    (O D : List Nat) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
      wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗ ⌜bkDone X X' w w' bl B O D st⌝) ∨
    (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
      ⌜spErr X X' w w' st⌝ ∗
      ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w'))))

/-- **`child.spill()` for a nested bucket** (see the module doc). -/
abbrev Bucket.spill.specC : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec)
    (O : List Nat) (h : Nat) (F D : List Nat) (N : List Loc),
  bkPre X w bl B O h F D N →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err; bkPost K tx r m X w bl B O D err }}

end spec

end defs

end Spill

end bbolt
end EtcdGrove
end Perennial
