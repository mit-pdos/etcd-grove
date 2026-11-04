/-
`Bucket.spill`'s root-bucket loop (U9q, `notes/bbolt-proof-plan.md`; U9n's design): **the loop
invariant**, pure. The root spill iterates over the root bucket's cached children (`B0.bm`, keys
`keys` in the iteration order); before the `i`-th key the writer's records are `X`, its side `w`,
the freelist `w0`'s after the steps `st`, and every child is in one of three states (`KSt`):

- `todo`: not yet visited; as at the start (its record live, no cached child, searchable, its
  logical tree finite; with a root node, the top of an unspilled tree over the current page map
  and mark, owning the slots `Dc k`, its base pages freeable, its elements its plain entries;
  without one, owning no slot: its base tree is the root's, `rootOwn`);
- `nilc`: visited without a root node (`continue`): nothing changed, no slot owned;
- `val v p`: visited, its new value `v` made (the inline value `Bucket.write` gives, or the header
  of the tree `child.spill()` wrote), a `bvalS` over the current page map whose pages' slots are
  `Dc k`, holding the child's entries at the start (`bvalData`); put into the root bucket's leaf
  (`p = true`) or not yet (`p = false`, between the child's spill and `c.node().put`).

Across all children: the root bucket's record (its `buckets` map unchanged, searchable, `rootLoc`),
the spill's global state (`spG`), the base pages and the committed state unchanged, the mark not
lower, and one slot invariant over the root's own slots `Lroot` (fixed at the start, their pages
unchanged) and the children's: every base slot owned or pending, every owned slot base or new;
the root bucket's bucket entries those at the start, the put values in place of the old ones.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSpec
public import Proof.go_etcd_io.bbolt.Spill.BktFinal
public import Proof.go_etcd_io.bbolt.Spill.BktSlot
public import Proof.go_etcd_io.bbolt.Spill.BktVal
public import Proof.go_etcd_io.bbolt.Spill.SlotInv
public import Proof.go_etcd_io.bbolt.Spill.StepComp
public import Proof.go_etcd_io.bbolt.Model.RTree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section inv
variable [GooseExts]

/-- A child's state in the root loop (see the module doc). -/
inductive KSt where
  | todo
  | nilc
  | val (v : List w8) (put : Bool)

/-- A leaf page's elements are plain (`plainTree`'s clause, for one page). -/
def plainPg (pg : List w8) : Prop :=
  ∀ j < pageCount pg,
    leafFlags pg j % 2 = 0 ∧ 0 < leafKsize pg j ∧ leafKsize pg j + leafVsize pg j ≤ bboltEntryMax

/-- **A nested bucket's new value holds the entries `E`, plain**: inline, its page's; else its
tree's (over `P`). -/
def bvalData (P : Pages) (v : List w8) (E : List BoltEnt) : Prop :=
  (inBucketRoot v = 0 → leafEnts (inlinePage v) = E ∧ plainPg (inlinePage v)) ∧
  (inBucketRoot v ≠ 0 → treeEntries P (inBucketRoot v) = E ∧ plainTree P (inBucketRoot v))

/-- **The root bucket's facts the loop keeps** (for its searches, and for its unspilled tree at
the end, `InitB`): searchable, its nodes non-empty below the root and branches of two entries,
its entries within `bboltEntryMax`, its logical tree finite. -/
def rootLoc (X : WX) (bl : Loc) : Prop :=
  bktLocalOK X bl ∧ rtOK X bl ∧ ∃ B, X.t.bs !! bl = some B ∧ ∀ l r, B.ns !! l = some r →
    ((r.nv.parent' ≠ null → 0 < r.ws.length) ∧ (r.nv.isLeaf' = false → 2 ≤ r.ws.length)) ∧
    ∀ w ∈ r.ws, 0 < w.key.length ∧ w.key.length + w.value.length ≤ bboltEntryMax

/-- **A child not yet visited** (see the module doc). -/
def childTodo (X0 X : WX) (w : WDb) (txid : w64) (c : Loc) (D : List Nat) : Prop :=
  ∃ C, X.t.bs !! c = some C ∧ c ∈ X.liveB ∧ C.bm = ∅ ∧ c ≠ X.rl ∧ bktLocalOK X c ∧ rtOK X c ∧
    lbktEnts X c = lbktEnts X0 c ∧
    (C.bv.rootNode' = null → D = [] ∧ ∃ C0, X0.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null) ∧
    (C.bv.rootNode' ≠ null → ∃ rn h F N E, X.node c C.bv.rootNode' = some rn ∧
      rn.nv.parent' = null ∧
      uTree X c (spP X) X.t.mv.pgid'.toNat C.bv.rootNode' none none h F D N E ∧
      spFree X w.fl txid F ∧ E.map (fun e => (e.2.1, e.2.2)) = lbktEnts X0 c ∧ plainEls E)

/-- **A child's state** (see the module doc). -/
def childSt (X0 X : WX) (w : WDb) (txid : w64) (c : Loc) (D : List Nat) : KSt → Prop
  | .todo => childTodo X0 X w txid c D
  | .nilc => D = [] ∧ ∃ C0, X0.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null
  | .val v _ => ∃ S, bvalS (spP X) X.t.mv.pgid'.toNat v S ∧ D = pgSlots (spP X) S ∧
      bvalData (spP X) v (lbktEnts X0 c)

/-- The value of a root entry after the loop's puts. -/
def KSt.entVal : KSt → List w8 → List w8
  | .val v true, _ => v
  | _, v0 => v0

/-- **The root loop's invariant** (see the module doc), from the start `(X0, w0)` (root record
`B0`, iteration order `keys`, the root's own slots `Lroot`), at `(X, w)` after the steps `st`, the
children's slots `Dc` and states `ks` (by name). -/
structure RInv (X0 : WX) (w0 : WDb) (B0 : BRec) (keys : List GoString) (Lroot : List Nat)
    (X : WX) (w : WDb) (st : List FLStep) (Dc : GoString → List Nat) (ks : GoString → KSt) :
    Prop where
  C : w.C = w0.C
  fl : w.fl = w0.fl.applySteps w0.wtxid st
  pages : X.v.pages = X0.v.pages
  rl : X.rl = X0.rl
  mark : X0.t.mv.pgid'.toNat ≤ X.t.mv.pgid'.toNat
  G : spG X w0.wtxid (mapLen w.ms) w.fl
  root : ∃ B, X.t.bs !! X0.rl = some B ∧ B.bv.buckets' = B0.bv.buckets' ∧ B.bm = B0.bm
  rootOK : rootLoc X X0.rl
  slots : slotInv w.fl X.t.mv.pgid'.toNat (Lroot ++ keys.flatMap Dc)
  base : ∀ s ∈ treeSlots w0.C, s ∈ Lroot ++ keys.flatMap Dc ∨ s ∈ pendSlots w.fl
  new : ∀ s ∈ Lroot ++ keys.flatMap Dc, s ∈ treeSlots w0.C ∨ newSlot st X0.t.mv.pgid'.toNat s
  agree : ∀ x ∈ Lroot, spP X !! x = spP X0 !! x
  kids : ∀ k c, B0.bm !! k = some c → childSt X0 X w w0.wtxid c (Dc k) (ks k)
  ents : rootEnts X = (rootEnts X0).map fun e => (e.1, (ks e.1).entVal e.2)

/-- The state before the `i`-th key: the keys before it visited and put, the others not. -/
def ksAt (keys : List GoString) (i : Nat) (ks : GoString → KSt) : Prop :=
  ∀ j k, keys[j]? = some k → (j < i → ks k ≠ .todo ∧ ∀ v, ks k ≠ .val v false) ∧
    (i ≤ j → ks k = .todo)

/-! ## The loop's start and end (statements; proofs to come) -/

/-- **The invariant at the start**: every child not visited, the root's own slots `rootOwn`
(U9p's `slotInv_start`), each child's its `bk_init` tree's. -/
theorem rinv_start {X : WX} {w : WDb} {B0 : BRec} (hpre : spillPre X w.fl) (hreach : liveReach X)
    (hml : X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms) (hfv : flViewU X w.fl)
    (hw : wdbOK w ∧ w.ms = some (X.v.base, mapLen w.ms) ∧ X.v = View.ofC X.v.base w.C)
    (hB0 : X.t.bs !! X.rl = some B0) (keys : List GoString)
    (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome) (hnd : keys.Nodup) :
    ∃ Lroot Dc, RInv X w B0 keys Lroot X w [] Dc (fun _ => .todo) := by
  sorry

/-- **The end, no root node**: nothing was put, the root bucket has no root node, and the records
are the spill's success as they are. -/
theorem rinv_end_nil {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' = null) :
    spillOK X0 X w0.C w0.fl w.fl w0.wtxid ∧ flViewU X w.fl := by
  sorry

/-- **The end, with a root node**: the root bucket's root node is the top of an unspilled tree
over the current page map and mark (`InitB`: its nested values `bvalS`, the visited children's new
ones, `BktVal`'s for the others), owning every owned slot (`O = []`); and after its spill and
`b.rootNode = root; SetRootPage` the spill's success. -/
theorem rinv_end {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' ≠ null) :
    ∃ rn h F D N E, rn.nv.spilled' = false ∧
      spPre X w X0.rl B.bv.rootNode' rn [] none none h F D N E .top ∧
      ∀ (X1 : WX) (w1 : WDb) (st1 : List FLStep) (B1 : BRec) (rt : Loc) (rr : NRec),
        spDone X X1 w w1 X0.rl B.bv.rootNode' rn [] none none h D N E .top st1 →
        X1.t.bs !! X0.rl = some B1 → B1.ns !! rt = some rr → rt ∈ X1.live →
        rr.nv.spilled' = true → rr.nv.parent' = null → nodeRootIn B1 B1.bv.rootNode' rt →
        spillOK X0 (X1.setBkt X0.rl (bkRooted B1 rt rr.nv.pgid')) w0.C w0.fl w1.fl w0.wtxid ∧
          flViewU (X1.setBkt X0.rl (bkRooted B1 rt rr.nv.pgid')) w1.fl := by
  sorry

end inv

end Spill

end bbolt
end EtcdGrove
end Perennial
