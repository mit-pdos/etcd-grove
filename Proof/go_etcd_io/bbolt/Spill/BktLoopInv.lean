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
public import Spec.go_etcd_io.bbolt.Bucket__spill
public import Proof.go_etcd_io.bbolt.Spill.BktSlot
public import Proof.go_etcd_io.bbolt.Spill.BktVal
public import Proof.go_etcd_io.bbolt.Spill.SlotInv
public import Proof.go_etcd_io.bbolt.Spill.StepComp
public import Proof.go_etcd_io.bbolt.Model.RTree
public import Proof.go_etcd_io.bbolt.Spill.BktRootPos
public import Proof.go_etcd_io.bbolt.Spill.BktLoopFreeNC

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
  ∃ C, X.t.bs !! c = some C ∧ c ∈ X.liveB ∧ C.bm = ∅ ∧ c ≠ X.rl ∧
    (C.bv.rootNode' ≠ null → bktLocalOK X c) ∧ rtOK X c ∧
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
      bvalData (spP X) v (lbktEnts X0 c) ∧ v.length ≤ 2 ^ 27

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
  rootIb : ∀ B, X.t.bs !! X0.rl = some B → B.ib = B0.ib
  slots : slotInv w.fl X.t.mv.pgid'.toNat (Lroot ++ keys.flatMap Dc)
  base : ∀ s ∈ treeSlots w0.C, s ∈ Lroot ++ keys.flatMap Dc ∨ s ∈ pendSlots w.fl
  new : ∀ s ∈ Lroot ++ keys.flatMap Dc, s ∈ treeSlots w0.C ∨ newSlot st X0.t.mv.pgid'.toNat s
  agree : ∀ x ∈ Lroot, spP X !! x = spP X0 !! x
  kids : ∀ k c, B0.bm !! k = some c → childSt X0 X w w0.wtxid c (Dc k) (ks k)
  ents : rootEnts X = (rootEnts X0).map fun e => (e.1, (ks e.1).entVal e.2)
  /-- Every cached child is iterated (its slots are among the owned ones). -/
  keysAll : ∀ k, (B0.bm !! k).isSome → k ∈ keys
  /-- The root bucket is not inline (`rootNotInline` at the start; its header kept, `rootIb`). -/
  rootPg : B0.ib.root' ≠ W64 0
  /-- The root bucket's entries' keys are not empty (the searches' keys, `node.put`'s premise). -/
  entKeys : ∀ we ∈ X.allEnts X0.rl, 0 < we.key.length ∧ we.key.length ≤ maxKeySize
  /-- The root's cached children are distinct (`StartFacts.inj`). -/
  inj : ∀ k k' c, B0.bm !! k = some c → B0.bm !! k' = some c → k = k'
  /-- The committed state's tree is well-formed (`StartFacts.cok`; the view's, `viewWF`). -/
  cok : treeOK w0.C
  /-- The buffers are dirty pages of fresh slots (`spillBufs`). -/
  bufs : bufsOK X w0.C w.fl
  /-- (U9x3) The root bucket's page positions are under its positions at the start (`rootUnder`:
  for `rootPage_shape`, with `shape0`). -/
  rootPos : ∀ B, X.t.bs !! X0.rl = some B → rootUnder X0.v.pages B0 B
  /-- (U9x3) The view leaf pages' shape under the root bucket's positions at the start (`wOKR`'s
  `posShape`). -/
  shape0 : ∀ c p pg, posRoot B0 c → ownHas X0.v.pages c p → X0.v.pages !! p = some pg →
    pageFlags pg = leafPageFlag → ∀ i < pageCount pg, 0 < leafKsize pg i ∧
      leafKsize pg i + leafVsize pg i ≤ bboltEntryMax ∧ leafKsize pg i ≤ maxKeySize
  /-- (U9x3) The committed mark at most the start's (`StartFacts.hwm`): the committed tree's
  slots below the mark (`treeSlots_lt`, `spPre`'s clause). -/
  hwm0 : w0.C.hwm ≤ X0.t.mv.pgid'.toNat
  /-- (U9x3) The start's free ids cover no committed page (`wdbOK`; `freeNoCov_steps` for `w.fl`,
  `spPre`'s clause). -/
  freeNC : ∀ y ∈ w0.fl.free, ¬ coversSlot w0.C.pages y.toNat
  /-- (U9x3) The transaction's struct unchanged (`Bucket.spill.spec`'s post). -/
  tt : X.t.t = X0.t.t
  /-- (U9x5) Before any value is staged, nothing has changed (`rinv_end_nil`). -/
  same : (∀ k ∈ keys, ∀ v p, ks k ≠ .val v p) → X = X0 ∧ w = w0 ∧ st = []
  /-- (U9x5) Once a value is put, the root bucket has a root node (`Cursor.node` materialized
  its root). -/
  putRoot : (∃ k v, ks k = .val v true) → ∀ B, X.t.bs !! X0.rl = some B → B.bv.rootNode' ≠ null
  /-- (U9x4) The meta copy but the high-water mark kept (`spFrame`'s meta clause; the spill's
  post). -/
  mvEq : X.t.mv = { X0.t.mv with pgid' := X.t.mv.pgid' }
  /-- (coordinator, for `rinv_end`'s `spPre`) The root's own base pages can be freed by the
  writer (`spFree`). -/
  rootFree : ∀ F : List Nat, (∀ id ∈ F, id ∈ Lroot ∧ (X0.v.pages !! id).isSome ∧ id < 2 ^ 62) →
    spFree X w.fl w0.wtxid F
  /-- (U9x7) The root's own slots are those `rinv_start` gave: the start's covered slots that no
  child's unspilled tree owned (`rootOwn`), the children's slots at the start `Dc0`. -/
  lroot : ∃ Dc0 : GoString → List Nat, Lroot = rootOwn X0 (keys.flatMap Dc0) ∧
    ∀ k c, B0.bm !! k = some c → childTodo X0 X0 w0 w0.wtxid c (Dc0 k)
  /-- (U9x7) The root bucket's extents (what `Bucket.free` would free: its positions' pages, each
  a materialized node's page or an unmaterialized page) are the start's: the loop's
  materializations give a node its position's page, a put into a leaf and a child's spill keep
  the root's logical tree's shape and page ids (`BktLoopExt`, `BktLoopExtMat`). With `lroot`,
  the root's own slots are covered by these extents, a cached child's at the start, or an
  unopened bucket's value (`lCovers`). -/
  rootExt : X.extents X0.rl = X0.extents X0.rl
  /-- (U9x7) A name not iterated is never visited. -/
  notKeys : ∀ k, k ∉ keys → ks k = .todo
  /-- (U9x7) A child with no root node at the start is skipped (`continue`: Go's `child.spill()`
  returns at once and `child.rootNode == nil`; it is not `inlineable`): `nilc`, or not yet
  visited and still without a root node. Never `val` (`rinv_nilKid`). -/
  nilKids : ∀ k c C0, B0.bm !! k = some c → X0.t.bs !! c = some C0 → C0.bv.rootNode' = null →
    ks k = .nilc ∨ (ks k = .todo ∧ ∀ C, X.t.bs !! c = some C → C.bv.rootNode' = null)
  /-- (U9x10) The root bucket's entries are bucket entries (`BktRootKeys.rootBkt_wOKR` at the
  start: `leafShape`, `posShape`; a materialization and a child's spill keep the entries by data,
  a put's `rootEnt` is a bucket's): for `endEls`'s root shape and names. -/
  rootBkt : ∀ we ∈ X.allEnts X0.rl, isBktFlag we.flags
  /-- (U9w6, D-K) The buffers grown over the mark's growth since the start (`markGrow`: the
  children's spills' steps; with `Bucket.spill.spec`'s `markCov` premise, its post's). -/
  grow : markGrow X0 X
  /-- (U9w7, for `Commit`'s `hbx`) The buffers' slots free at the start or at or above the start's
  mark (`bufSrc`: the children's spills' steps' `srcGrow`; with `spillStartOK`'s committed mark at
  most the start's, `Bucket.spill.spec`'s source conjunct). -/
  src : bufSrc X w0.fl.free X0.t.mv.pgid'.toNat

/-- **A child with no root node at the start never gets a value** (`RInv.nilKids`). -/
theorem rinv_nilKid {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc} {C0 : BRec}
    (hc : B0.bm !! k = some c) (hC0 : X0.t.bs !! c = some C0) (hn : C0.bv.rootNode' = null)
    (v : List w8) (p : Bool) : ks k ≠ .val v p := by
  intro e
  rcases hI.nilKids k c C0 hc hC0 hn with h | ⟨h, -⟩ <;> rw [e] at h <;> cases h

/-- The state before the `i`-th key: the keys before it visited and put, the others not. -/
def ksAt (keys : List GoString) (i : Nat) (ks : GoString → KSt) : Prop :=
  ∀ j k, keys[j]? = some k → (j < i → ks k ≠ .todo ∧ ∀ v, ks k ≠ .val v false) ∧
    (i ≤ j → ks k = .todo)

/-- `f` with `k` mapped to `b`. -/
def upd {β : Type} (f : GoString → β) (k : GoString) (b : β) : GoString → β :=
  fun k' => if k' = k then b else f k'

/-- The slots owned by everything but the child `k`: the root's and the other children's. -/
def othersO (Lroot : List Nat) (keys : List GoString) (Dc : GoString → List Nat)
    (k : GoString) : List Nat :=
  Lroot ++ (keys.filter fun k' => decide (k' ≠ k)).flatMap Dc

/-- **`RInv.notKeys` through a visit of an iterated key.** -/
theorem notKeys_upd {keys : List GoString} {ks : GoString → KSt} {k : GoString} {s : KSt}
    (h : ∀ k, k ∉ keys → ks k = .todo) (hk : k ∈ keys) :
    ∀ k', k' ∉ keys → upd ks k s k' = .todo := by
  intro k' hk'
  unfold upd
  rw [if_neg (fun e => hk' (by rw [e]; exact hk))]; exact h k' hk'

/-- **`RInv.nilKids` through a step** to `X'` that sets `k`'s state to `s`: `k`'s own case, and
the other todo children's records keep no root node. -/
theorem nilKids_upd {X0 X X' : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {s : KSt}
    (hself : ∀ c C0, B0.bm !! k = some c → X0.t.bs !! c = some C0 → C0.bv.rootNode' = null →
      s = .nilc ∨ (s = .todo ∧ ∀ C, X'.t.bs !! c = some C → C.bv.rootNode' = null))
    (hother : ∀ k' c' C, k' ≠ k → B0.bm !! k' = some c' → ks k' = .todo →
      X.t.bs !! c' = some C → C.bv.rootNode' = null →
      ∀ C', X'.t.bs !! c' = some C' → C'.bv.rootNode' = null) :
    ∀ k' c C0, B0.bm !! k' = some c → X0.t.bs !! c = some C0 → C0.bv.rootNode' = null →
      upd ks k s k' = .nilc ∨
      (upd ks k s k' = .todo ∧
        ∀ C, X'.t.bs !! c = some C → C.bv.rootNode' = null) := by
  intro k' c C0 hc hC0 hn
  unfold upd
  by_cases e : k' = k
  · subst e; rw [if_pos rfl]; exact hself c C0 hc hC0 hn
  · rw [if_neg e]
    rcases hI.nilKids k' c C0 hc hC0 hn with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      have hk := hI.kids k' c hc
      rw [h1] at hk
      obtain ⟨C, hC, -⟩ := hk
      exact hother k' c C e hc h1 hC (h2 C hC)

/-- `nilKids_upd`'s own case for a visited child that had a root node. -/
theorem nilKids_self_todo {X0 X X' : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc} {C : BRec}
    (hks : ks k = .todo) (hc : B0.bm !! k = some c) (hC : X.t.bs !! c = some C)
    (hnn : C.bv.rootNode' ≠ null) (s : KSt) :
    ∀ c0 C0, B0.bm !! k = some c0 → X0.t.bs !! c0 = some C0 → C0.bv.rootNode' = null →
      s = .nilc ∨ (s = .todo ∧ ∀ C, X'.t.bs !! c0 = some C → C.bv.rootNode' = null) := by
  intro c0 C0 hc0 hC0 hn
  rw [hc] at hc0; cases hc0
  rcases hI.nilKids k c C0 hc hC0 hn with h | ⟨-, h⟩
  · rw [hks] at h; cases h
  · exact absurd (h C hC) hnn

/-- `nilKids_upd`'s own case for a child with a staged value. -/
theorem nilKids_self_val {X0 X X' : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {v : List w8} {p : Bool}
    (hks : ks k = .val v p) (s : KSt) :
    ∀ c0 C0, B0.bm !! k = some c0 → X0.t.bs !! c0 = some C0 → C0.bv.rootNode' = null →
      s = .nilc ∨ (s = .todo ∧ ∀ C, X'.t.bs !! c0 = some C → C.bv.rootNode' = null) := by
  intro c0 C0 hc0 hC0 hn
  rcases hI.nilKids k c0 C0 hc0 hC0 hn with h | ⟨h, -⟩ <;> rw [hks] at h <;> cases h

theorem upd_same {β : Type} (f : GoString → β) (k : GoString) (b : β) : upd f k b k = b := by
  unfold upd; rw [if_pos rfl]

/-- Meta copies but the high-water mark compose (`RInv.mvEq`). -/
theorem mv_trans {a b c : Meta} (h1 : b = { a with pgid' := b.pgid' })
    (h2 : c = { b with pgid' := c.pgid' }) : c = { a with pgid' := c.pgid' } := by
  have e : ({ b with pgid' := c.pgid' } : Meta) = { a with pgid' := c.pgid' } := by
    rw [h1]
  exact h2.trans e

/-- `RInv.same`'s premise fails once a key's value is staged. -/
theorem same_upd_val {keys : List GoString} {ks : GoString → KSt} {k : GoString} (hk : k ∈ keys)
    (v : List w8) (p : Bool) : ¬ ∀ k' ∈ keys, ∀ v' p', upd ks k (.val v p) k' ≠ .val v' p' :=
  fun h => h k hk v p (upd_same ks k _)

/-- `RInv.same`'s premise through a visit of a todo key that stages nothing. -/
theorem same_upd_nv {keys : List GoString} {ks : GoString → KSt} {k : GoString} {s : KSt}
    (hks : ks k = .todo) (h : ∀ k' ∈ keys, ∀ v p, upd ks k s k' ≠ .val v p) :
    ∀ k' ∈ keys, ∀ v p, ks k' ≠ .val v p := by
  intro k' hk' v p e
  by_cases h' : k' = k
  · subst h'; rw [hks] at e; cases e
  · apply h k' hk' v p; unfold upd; rw [if_neg h']; exact e

/-- `RInv.putRoot`'s premise through a state change that puts nothing. -/
theorem putRoot_upd {ks : GoString → KSt} {k : GoString} {s : KSt} (hs : ∀ v, s ≠ .val v true)
    (h : ∃ k' v, upd ks k s k' = .val v true) : ∃ k' v, ks k' = .val v true := by
  obtain ⟨k', v, e⟩ := h
  by_cases h' : k' = k
  · subst h'; rw [upd_same] at e; exact absurd e (hs v)
  · unfold upd at e; rw [if_neg h'] at e; exact ⟨k', v, e⟩

theorem flatMap_perm_split {β : Type} {keys : List GoString} {Dc : GoString → List β}
    {k : GoString} (hnd : keys.Nodup) (hk : k ∈ keys) :
    (keys.flatMap Dc).Perm ((keys.filter fun k' => decide (k' ≠ k)).flatMap Dc ++ Dc k) := by
  induction keys with
  | nil => cases hk
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons]
    by_cases e : a = k
    · subst e
      have hf : t.filter (fun k' => decide (k' ≠ a)) = t :=
        List.filter_eq_self.2 (fun x hx => by simp only [decide_eq_true_eq]; intro h; subst h; exact hnd.1 hx)
      rw [List.filter_cons_of_neg (by simp), hf]
      exact List.perm_append_comm
    · have hk' : k ∈ t := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h.symm e
        · exact h
      rw [List.filter_cons_of_pos (by simpa using e), List.flatMap_cons, List.append_assoc]
      exact List.Perm.append_left _ (ih hnd.2 hk')

/-- **The free ids cover no committed page** (`spPre`'s clause, from `RInv.freeNC`). -/
theorem rinv_freeNC {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) :
    ∀ y ∈ w.fl.free, ¬ coversSlot w.C.pages y.toNat := by
  rw [hI.fl, hI.C]; exact freeNoCov_steps hI.freeNC _ _

/-- **The committed tree's slots lie below the mark** (`spPre`'s clause). -/
theorem rinv_treeLt {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) :
    ∀ s ∈ treeSlots w.C, s < X.t.mv.pgid'.toNat := by
  rw [hI.C]; exact treeSlots_lt hI.cok (Nat.le_trans hI.hwm0 hI.mark)

end inv

end Spill

end bbolt
end EtcdGrove
end Perennial
