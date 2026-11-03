/-
The writer's logical tree and its data (U0a of `notes/bbolt-proof-plan.md`; design §3.2,
§3.10): each bucket's tree is the base view's pages overlaid with the materialized nodes
(`ltree X bl pid`: the entries at position `pid` of bucket `bl`, from its node if materialized,
else from the view's page), and `wtxData X` the data it holds: the root bucket's bucket entries,
each with its bucket's logical entries (an opened bucket's) or its base tree's (an unopened
one's).

The statements are the data lemmas of the writer's operations (U7, U8, U9) and the stability of
leaf contents (R6, U6).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Wtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section ltree
variable [GooseExts]

/-- The entry a writer reads from element `i` of page `pg` (`ReadInodeFromPage`; its bytes in
the view). -/
def pageW (pg : List w8) (i : Nat) : WEntry :=
  if pageFlags pg = leafPageFlag then
    ⟨W32 (leafFlags pg i : Int), W64 0, leafKey pg i, leafValue pg i, Src.view, Src.view⟩
  else ⟨W32 0, W64 (branchPgid pg i : Int), branchKey pg i, [], Src.view, Src.own DFrac.discard⟩

/-- The entries of page `pg`. -/
def pageWs (pg : List w8) : List WEntry := (List.range (pageCount pg)).map (pageW pg)

/-- **The logical tree**: at each bucket (by location) and position (page id; `0` for an inline
bucket's root), whether it is a leaf and its entries. -/
abbrev LTree := Loc → w64 → Option (Bool × List WEntry)

/-- The writer's logical tree: a materialized node's entries, else the view's page's. -/
def ltree (X : WX) : LTree := fun bl pid =>
  match X.t.bs !! bl with
  | none => none
  | some B =>
    match resolve B pid with
    | some l => (B.ns !! l).map fun r => (r.nv.isLeaf', r.ws)
    | none => (wpageAt X.v B pid).map fun lp => (decide (pageFlags lp.2 = leafPageFlag), pageWs lp.2)

/-- The leaves of the logical tree of bucket `bl` from position `pid`, in order (`fuel` bounds
the depth). -/
def lleaves (L : LTree) (bl : Loc) : Nat → w64 → List (List WEntry)
  | 0, _ => []
  | n + 1, pid =>
    match L bl pid with
    | some (true, ws) => [ws]
    | some (false, ws) => ws.flatMap fun w => lleaves L bl n w.pgid
    | none => []

/-- The fuel of a walk of `X`'s logical trees. -/
def WX.fuel (X : WX) : Nat := X.v.pages.size + X.t.bs.size + 1

/-- The root position of bucket `bl`. -/
def WX.rootPid (X : WX) (bl : Loc) : w64 := ((X.t.bs !! bl).map fun B => B.ib.root').getD 0

/-- The leaves of bucket `bl`'s logical tree. -/
def WX.leaves (X : WX) (bl : Loc) : List (List WEntry) :=
  lleaves (ltree X) bl X.fuel (X.rootPid bl)

/-- The plain entries of bucket `bl`, in order. -/
def lbktEnts (X : WX) (bl : Loc) : List BoltEnt :=
  (X.leaves bl).flatMap fun ws => ws.filterMap fun w =>
    if decide (isBktFlag w.flags) then none else some (w.key, w.value)

/-- The bucket entries of the root bucket (name, value), in order. -/
def rootEnts (X : WX) : List (GoString × List w8) :=
  (X.leaves X.rl).flatMap fun ws => ws.filterMap fun w =>
    if decide (isBktFlag w.flags) then some (w.key, w.value) else none

/-- The contents of the top-level bucket `n` whose value is `v`: its logical entries if it is
opened in the root bucket, else its base tree's. -/
def bktDataOf (X : WX) (n : GoString) (v : List w8) : BktData :=
  match (X.t.bs !! X.rl).bind (fun B => B.bm !! n) with
  | some c => GMap.ofList (lbktEnts X c)
  | none => bktOfPage X.v.pages v

/-- The data of the top-level bucket `n`, if any. -/
def bktData (X : WX) (n : GoString) : Option BktData :=
  ((rootEnts X).find? fun e => decide (e.1 = n)).map fun e => bktDataOf X n e.2

/-- **The writer's data** (`T.cur`). -/
def wtxData (X : WX) : Data :=
  GMap.ofList ((rootEnts X).map fun e => (e.1, bktDataOf X e.1 e.2))

/-- The location of the opened top-level bucket `n` (a handle's bucket). -/
def bktLoc (X : WX) (n : GoString) : Option Loc := (X.t.bs !! X.rl).bind fun B => B.bm !! n

/-- `X` with node `l` of bucket `bl` holding the entries `ws'` (only the logical content; the
struct and inodes are the operation's). -/
def WX.withWs (X : WX) (bl l : Loc) (ws' : List WEntry) : WX :=
  { X with t := { X.t with bs :=
    match X.t.bs !! bl with
    | none => X.t.bs
    | some B => X.t.bs.insert bl { B with ns :=
        match B.ns !! l with
        | none => B.ns
        | some r => B.ns.insert l { r with ws := ws' } } } }

/-- The entries of node `l` of bucket `bl`. -/
def nodeWs (X : WX) (bl l : Loc) : Option (List WEntry) :=
  (X.t.bs !! bl).bind fun B => (B.ns !! l).map NRec.ws

/-- `ws` with the entry `e` put (replacing an entry of its key; sorted `ws` stays sorted). -/
def wsPut (ws : List WEntry) (e : WEntry) : List WEntry :=
  ws.filter (fun w => decide (go.GoStringLt w.key e.key)) ++ [e] ++
    ws.filter (fun w => decide (go.GoStringLt e.key w.key))

/-- `ws` without the entry of key `k`. -/
def wsDel (ws : List WEntry) (k : List w8) : List WEntry := ws.filter fun w => decide (w.key ≠ k)

/-- The materialized leaf `l` of bucket `bl` is where a search for `k` lands (`k` within its
bounds, `bktKeysB`). -/
def leafFor (X : WX) (bl : Loc) (k : List w8) (l : Loc) : Prop :=
  ∃ B r bnd, X.t.bs !! bl = some B ∧ B.ns !! l = some r ∧ r.nv.isLeaf' = true ∧
    bktKeysB X.v B bnd ∧ keyIn (bnd l).1 (bnd l).2 k

/-! ## Lemma statements -/

/-- **`Put`'s data** (U7): putting a plain entry `(k, v)` into the leaf where `k` lands, in the
opened bucket `n`, sets `k` to `v` in bucket `n`. -/
theorem wtxData_put (X : WX) (n : GoString) (bl l : Loc) (ws : List WEntry) (e : WEntry)
    (hok : wOK X) (hb : bktLoc X n = some bl) (hl : leafFor X bl e.key l)
    (hws : nodeWs X bl l = some ws) (hflag : ¬ isBktFlag e.flags) (hk : e.key ≠ [])
    (hnb : ∀ w ∈ ws, w.key = e.key → ¬ isBktFlag w.flags) :
    wtxData (X.withWs bl l (wsPut ws e)) =
      (wtxData X).insert n (((wtxData X) !! n).getD ∅ |>.insert e.key e.value) := by
  sorry

/-- **`Delete`'s data** (U7): deleting the plain entry `k` from the leaf where `k` lands. -/
theorem wtxData_del (X : WX) (n : GoString) (bl l : Loc) (ws : List WEntry) (k : List w8)
    (hok : wOK X) (hb : bktLoc X n = some bl) (hl : leafFor X bl k l)
    (hws : nodeWs X bl l = some ws) (hnb : ∀ w ∈ ws, w.key = k → ¬ isBktFlag w.flags) :
    wtxData (X.withWs bl l (wsDel ws k)) =
      (wtxData X).insert n (((wtxData X) !! n).getD ∅ |>.delete k) := by
  sorry

/-- **`CreateBucket`'s data** (U7): the root's entries gain `n`, whose bucket is empty, and
the other buckets are unchanged. -/
theorem wtxData_create (X X' : WX) (n : GoString) (hok : wOK X) (hok' : wOK X')
    (hnew : (wtxData X) !! n = none)
    (hn : bktData X' n = some ∅)
    (hnames : ∀ n', n' ≠ n → bktData X' n' = bktData X n') :
    wtxData X' = (wtxData X).insert n ∅ := by
  sorry

/-- **`DeleteBucket`'s data** (U7): the root's entry `n` is gone, the other buckets
unchanged. -/
theorem wtxData_drop (X X' : WX) (n : GoString) (hok : wOK X) (hok' : wOK X')
    (hn : bktData X' n = none)
    (hnames : ∀ n', n' ≠ n → bktData X' n' = bktData X n') :
    wtxData X' = (wtxData X).delete n := by
  sorry

/-- **`rebalance` keeps the data** (U8): the root's bucket entries and every bucket's logical
entries in order are unchanged (merges, removals and the root collapse move entries between
nodes, never reorder or drop them). -/
theorem wtxData_rebalance (X X' : WX) (hok : wOK X)
    (hroot : rootEnts X' = rootEnts X)
    (hbkts : ∀ n, bktLoc X' n = bktLoc X n)
    (hents : ∀ n bl, bktLoc X n = some bl → lbktEnts X' bl = lbktEnts X bl) :
    wtxData X' = wtxData X := by
  sorry

/-- **The spilled tree holds the writer's data** (U9, the spill post's data clause): a
`treeOK` committed state whose root bucket names the writer's top-level buckets, each written
with its logical entries. -/
theorem treeData_spill (X : WX) (C' : CommitSt) (hok : wOK X) (htree : treeOK C')
    (hnames : (treeEntries C'.pages C'.root).map Prod.fst = (rootEnts X).map Prod.fst)
    (hbkts : ∀ n v, (n, v) ∈ treeEntries C'.pages C'.root →
      some (bktOfPage C'.pages v) = bktData X n) :
    treeData C' = wtxData X := by
  sorry

open Classical in
/-- **R6: a writer's leaf contents are a function of the base shape and `T.cur`** (before
`Commit`, branch keys never change and routing fixes which leaf holds a key): the plain entries
of a logical leaf of bucket `n` are the entries of `bktEnts (T.cur n)` within the leaf's bounds.
Used by U6 (stale cursor stacks stay valid at an unchanged `T`). -/
theorem ltree_leaf_of_T (X : WX) (n : GoString) (bl : Loc) (pid : w64) (ws : List WEntry)
    (hok : wOK X) (hb : bktLoc X n = some bl) (hl : ltree X bl pid = some (true, ws)) :
    ∃ lo hi, ws.filterMap (fun w => if decide (isBktFlag w.flags) then none
        else some (w.key, w.value)) =
      (bktEnts (((wtxData X) !! n).getD ∅)).filter fun e => decide (keyIn lo hi e.1) := by
  sorry

end ltree

end bbolt
end EtcdGrove
end Perennial
