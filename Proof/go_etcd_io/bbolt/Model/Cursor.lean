/-
Cursor stacks relative to a view and a transaction's data (U0a of `notes/bbolt-proof-plan.md`;
design §3.10, §3.13 "Cursor stacks (B5)").

A cursor's stack (`[]elemRef`: a page or a node, and an index) is a root-to-leaf path in a
bucket's tree. Its **shape** is read in the base view: a branch's children are its page's (a
materialized branch node has its page's entries before `Commit`, `nodePg`), so a path is a list
of page ids (`pids`), each element a page reference of the view or a node reference whose page id
the node-location registry `nl` records. Its **position** over the bucket's entries `es` (sorted:
`bktEnts`) is the number of entries below the leaf's lower bound (the base branch keys' bounds
along the path) plus the leaf index: a leaf's entries are those of `es` within its bounds (for a
reader by `treeKeys`; for a writer by R6, `ltree_leaf_of_T`). An empty leaf has the position of
the next one, which is why `next`'s skipping of empty leaves keeps it.

`rStackAt` (readers: page references only, `es` the view's) and `wStackAt` (writers: `es` from
`T.cur`, node references through the registry) are the two instances (B5).
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section cursor
variable [GooseExts]

/-- The location of page `pid` of the view. -/
def pageLoc (v : View) (pid : Nat) : Loc := v.base +ₗ ((pid * 4096 : Nat) : Int)

/-- The value of the top-level bucket `n` in the view (its root bucket's entry). -/
def baseVal (v : View) (n : GoString) : Option (List w8) :=
  ((treeEntries v.pages v.root).find? fun e => decide (e.1 = n)).map Prod.snd

/-- The root page of bucket `n` in the base view (`0`: inline, or not in the view: created by
the transaction). -/
def baseRoot (v : View) (n : GoString) : Nat := ((baseVal v n).map inBucketRoot).getD 0

/-- The keys of page `pid` of the view. -/
def pidKeys (v : View) (pid : Nat) : List (List w8) :=
  match v.pages !! pid with
  | some pg => (List.range (pageCount pg)).map (pageKey pg)
  | none => []

/-- **The shape of a stack**: `pids` (one per element) is a root-to-leaf path of bucket `n`'s
base tree, and each element refers to its page (a page of the view; for the inline root, a
location in the view) or to a node of bucket `b` read from it (registry `nl`). -/
def sPath (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (n : GoString)
    (els : List elemRef) (pids : List Nat) : Prop :=
  els ≠ [] ∧ pids.length = els.length ∧ pids.head? = some (baseRoot v n) ∧
  ∀ j e pid, els[j]? = some e → pids[j]? = some pid →
    (e.node' ≠ null → nl e.node' = some (b, pid)) ∧
    (e.node' = null → e.page' ≠ null ∧ (pid ≠ 0 → e.page' = pageLoc v pid)) ∧
    (j + 1 < els.length → ∃ pg, v.pages !! pid = some pg ∧ pageFlags pg = branchPageFlag ∧
      e.index'.toNat < pageCount pg ∧ pids[j + 1]? = some (branchPgid pg e.index'.toNat)) ∧
    (j + 1 = els.length → pid = 0 ∨ ∃ pg, v.pages !! pid = some pg ∧
      pageFlags pg = leafPageFlag)

/-- The bounds below a path from the bounds `b`: `entryBnd` along its branches' keys. -/
def pathBndFrom (v : View) (b : Option (List w8) × Option (List w8)) :
    List Nat → List elemRef → Option (List w8) × Option (List w8)
  | pid :: pid' :: ps, e :: es =>
    pathBndFrom v (entryBnd b (pidKeys v pid) e.index'.toNat) (pid' :: ps) es
  | _, _ => b

/-- The bounds of the leaf a path reaches. -/
def pathBnd (v : View) (pids : List Nat) (els : List elemRef) :
    Option (List w8) × Option (List w8) :=
  pathBndFrom v (none, none) pids els

/-- The leaf index of a stack (its last element's). -/
def leafIdx (els : List elemRef) : Nat := ((els.getLast?).map fun e => e.index'.toNat).getD 0

open Classical in
/-- The entries of `es` within the bounds `bnd` (a leaf's entries). -/
def entsIn (es : List BoltEnt) (bnd : Option (List w8) × Option (List w8)) : List BoltEnt :=
  es.filter fun e => decide (keyIn bnd.1 bnd.2 e.1)

open Classical in
/-- The position a path denotes over `es`: the entries below the leaf's lower bound, plus the
leaf index. -/
def stackPos (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) : Nat :=
  (es.filter fun e => decide (¬ keyGe (pathBnd v pids els).1 e.1)).length + leafIdx els

/-- **A stack at a position**: unpositioned (any stack), or a path whose position is `i` (at
most `es.length`: past the last, `Next` stays at `es.length`). -/
def stackAt (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc)
    (n : GoString) (els : List elemRef) : Option Nat → Prop
  | none => True
  | some i => ∃ pids, sPath nl v b n els pids ∧ i = min (stackPos v es pids els) es.length

/-- **A reader's stack** in bucket `n` of its view `v` (page references only). -/
def rStackAt (v : View) (n : GoString) (els : List elemRef) (pos : Option Nat) : Prop :=
  stackAt (fun _ => none) v (bktEnts ((v.data !! n).getD ∅)) null n els pos ∧
    ∀ e ∈ els, e.node' = null

/-- **A writer's stack** in bucket `n` (handle `b`) at the view `T`, over the base view `v` and
the node-location registry `nl` (B5, N3). -/
def wStackAt (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView) (b : Loc) (n : GoString)
    (els : List elemRef) (pos : Option Nat) : Prop :=
  stackAt nl v (bktEnts ((T.cur !! n).getD ∅)) b n els pos

/-! ## Moves -/

/-- At each branch the index a search for `k` descends to (the last whose key is at most `k`,
or the first: `routes` of `WriteTxShape`), and at the leaf the first entry not below `k`. -/
def sRoutes (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (k : List w8) : Prop :=
  (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
    let ks := pidKeys v pid
    e.index'.toNat < ks.length ∧
    (e.index'.toNat = 0 ∨ ∃ ki, ks[e.index'.toNat]? = some ki ∧ ¬ go.GoStringLt k ki) ∧
    ∀ kn, ks[e.index'.toNat + 1]? = some kn → go.GoStringLt k kn) ∧
  leafIdx els = ((entsIn es (pathBnd v pids els)).takeWhile
    fun e => decide (go.GoStringLt e.1 k)).length

/-- Every index of the stack is the first. -/
def sFirst (els : List elemRef) : Prop := ∀ e ∈ els, e.index'.toNat = 0

/-- Every branch index of the stack is the last, and so is the leaf's (over `es`). -/
def sLast (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) : Prop :=
  (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
    e.index'.toNat + 1 = (pidKeys v pid).length) ∧
  leafIdx els + 1 = (entsIn es (pathBnd v pids els)).length

/-- `els'` (path `pids'`) is the in-order successor of `els`: equal above some depth `d`, one
further at `d`, first below. -/
def sSucc (els els' : List elemRef) : Prop :=
  ∃ d, d < els.length ∧ d < els'.length ∧
    (els'.take d).map (·.index') = (els.take d).map (·.index') ∧
    (∃ e e', els[d]? = some e ∧ els'[d]? = some e' ∧ e'.index'.toNat = e.index'.toNat + 1) ∧
    ∀ j e', d < j → els'[j]? = some e' → e'.index'.toNat = 0

/-- `els'` is the in-order predecessor of `els`: equal above some depth `d`, one before at `d`,
last below (over the base pages and, at the leaf, `es`). -/
def sPred (v : View) (es : List BoltEnt) (pids' : List Nat) (els els' : List elemRef) : Prop :=
  ∃ d, d < els.length ∧ d < els'.length ∧
    (els'.take d).map (·.index') = (els.take d).map (·.index') ∧
    (∃ e e', els[d]? = some e ∧ els'[d]? = some e' ∧ e'.index'.toNat + 1 = e.index'.toNat) ∧
    ∀ j, d < j → j < els'.length → sLast v es (pids'.drop j) (els'.drop j)

/-! ## Lemma statements (U6) -/

/-- `Seek`'s descent reaches `seekIdx` (readers). -/
theorem rStackAt_seek (v : View) (n : GoString) (els : List elemRef) (pids : List Nat)
    (k : List w8) (hv : viewWF v) (hp : sPath (fun _ => none) v null n els pids)
    (hnode : ∀ e ∈ els, e.node' = null)
    (hr : sRoutes v (bktEnts ((v.data !! n).getD ∅)) pids els k) :
    rStackAt v n els (some (seekIdx (bktEnts ((v.data !! n).getD ∅)) k)) := by
  sorry

theorem rStackAt_first (v : View) (n : GoString) (els : List elemRef) (pids : List Nat)
    (hv : viewWF v) (hp : sPath (fun _ => none) v null n els pids)
    (hnode : ∀ e ∈ els, e.node' = null) (hf : sFirst els) :
    rStackAt v n els (some 0) := by
  sorry

theorem rStackAt_last (v : View) (n : GoString) (els : List elemRef) (pids : List Nat)
    (hv : viewWF v) (hp : sPath (fun _ => none) v null n els pids)
    (hnode : ∀ e ∈ els, e.node' = null)
    (hl : sLast v (bktEnts ((v.data !! n).getD ∅)) pids els) :
    rStackAt v n els (some ((bktEnts ((v.data !! n).getD ∅)).length - 1)) := by
  sorry

theorem rStackAt_next (v : View) (n : GoString) (els els' : List elemRef) (pids' : List Nat)
    (i : Nat) (hv : viewWF v) (h : rStackAt v n els (some i))
    (hp : sPath (fun _ => none) v null n els' pids') (hnode : ∀ e ∈ els', e.node' = null)
    (hs : sSucc els els') :
    rStackAt v n els' (some (min (i + 1) (bktEnts ((v.data !! n).getD ∅)).length)) := by
  sorry

theorem rStackAt_prev (v : View) (n : GoString) (els els' : List elemRef) (pids' : List Nat)
    (i : Nat) (hv : viewWF v) (h : rStackAt v n els (some i)) (hi : 0 < i)
    (hp : sPath (fun _ => none) v null n els' pids') (hnode : ∀ e ∈ els', e.node' = null)
    (hs : sPred v (bktEnts ((v.data !! n).getD ∅)) pids' els els') :
    rStackAt v n els' (some (i - 1)) := by
  sorry

/-- The writer's facts the writer lemmas take: `X` well-formed, `T.cur` its data, its base view
`v`, its registry at least `nl`, `b` the handle of bucket `n`. -/
def wCtx (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView) (b : Loc)
    (n : GoString) : Prop :=
  wOK X ∧ T.cur = wtxData X ∧ X.v = v ∧ (∀ x y, nl x = some y → X.nloc !! x = some y) ∧
    bktLoc X n = some b

theorem wStackAt_seek (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els : List elemRef) (pids : List Nat) (k : List w8)
    (hc : wCtx X nl v T b n) (hp : sPath nl v b n els pids)
    (hr : sRoutes v (bktEnts ((T.cur !! n).getD ∅)) pids els k) :
    wStackAt nl v T b n els (some (seekIdx (bktEnts ((T.cur !! n).getD ∅)) k)) := by
  sorry

theorem wStackAt_first (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els : List elemRef) (pids : List Nat)
    (hc : wCtx X nl v T b n) (hp : sPath nl v b n els pids) (hf : sFirst els) :
    wStackAt nl v T b n els (some 0) := by
  sorry

theorem wStackAt_last (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els : List elemRef) (pids : List Nat)
    (hc : wCtx X nl v T b n) (hp : sPath nl v b n els pids)
    (hl : sLast v (bktEnts ((T.cur !! n).getD ∅)) pids els) :
    wStackAt nl v T b n els (some ((bktEnts ((T.cur !! n).getD ∅)).length - 1)) := by
  sorry

/-- `next` (with its skipping of empty leaves, which keeps the position). -/
theorem wStackAt_next (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els els' : List elemRef) (pids' : List Nat) (i : Nat)
    (hc : wCtx X nl v T b n) (h : wStackAt nl v T b n els (some i))
    (hp : sPath nl v b n els' pids') (hs : sSucc els els') :
    wStackAt nl v T b n els' (some (min (i + 1) (bktEnts ((T.cur !! n).getD ∅)).length)) := by
  sorry

/-- **A stack stays valid at the same `T` as the registry grows** (R6). -/
theorem wStackAt_stable (nl nl' : Loc → Option (Loc × Nat)) (v : View) (T : TxView) (b : Loc)
    (n : GoString) (els : List elemRef) (pos : Option Nat)
    (hgrow : ∀ x y, nl x = some y → nl' x = some y) (h : wStackAt nl v T b n els pos) :
    wStackAt nl' v T b n els pos := by
  sorry

end cursor

end bbolt
end EtcdGrove
end Perennial
