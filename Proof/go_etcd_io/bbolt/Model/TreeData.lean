/-
The data a committed tree holds (U0a of `notes/bbolt-proof-plan.md`; design §3.2): `treeData C`,
the decoding of the pages into `Data` (the root bucket's leaves' bucket entries, each bucket's
leaves' entries in key order).

The walks are by fuel (the number of pages, enough for a well-formed tree, whose depth is at most
its number of pages); on a malformed tree they are arbitrary but total.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Tree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

section data
variable [GooseExts]

/-- The leaf pages of the tree from `id`, in order, through branches only (`fuel` bounds the
depth). -/
def leavesF : Nat → Pages → Nat → List (List w8)
  | 0, _, _ => []
  | n + 1, P, id =>
    match P !! id with
    | none => []
    | some pg =>
      if pageFlags pg = leafPageFlag then [pg]
      else (List.range (pageCount pg)).flatMap fun i => leavesF n P (branchPgid pg i)

/-- The leaf pages of the bucket tree from `root`, in order. -/
def treeLeaves (P : Pages) (root : Nat) : List (List w8) := leavesF (P.size + 1) P root

/-- A leaf page's entries: its elements' keys and values. -/
def leafEnts (pg : List w8) : List BoltEnt :=
  (List.range (pageCount pg)).map fun i => (leafKey pg i, leafValue pg i)

/-- The entries of the bucket tree from `root`, in order (in key order for a well-formed tree:
`treeKeys`). -/
def treeEntries (P : Pages) (root : Nat) : List BoltEnt := (treeLeaves P root).flatMap leafEnts

/-- The leaf pages of the nested bucket whose value is `v`: its inline page, or its tree's. -/
def bktLeaves (P : Pages) (v : List w8) : List (List w8) :=
  if inBucketRoot v = 0 then [inlinePage v] else treeLeaves P (inBucketRoot v)

/-- The entries of the nested bucket whose value is `v`, in order. -/
def bktEntries (P : Pages) (v : List w8) : List BoltEnt := (bktLeaves P v).flatMap leafEnts

/-- The contents of the nested bucket whose value (the root's leaf element's) is `v`. -/
def bktOfPage (P : Pages) (v : List w8) : BktData := GMap.ofList (bktEntries P v)

/-- **The data the committed state holds**: each top-level bucket (an entry of the root
bucket's tree) with its contents. -/
def treeData (C : CommitSt) : Data :=
  GMap.ofList ((treeEntries C.pages C.root).map fun e => (e.1, bktOfPage C.pages e.2))

/-! ## Lemma statements (U6) -/

/-- **A bucket's sorted entries are its tree's in-order leaves**: in a `treeOK` state, the
bucket `n` of `treeData C` is the bucket of the root's entry `n`, and its `bktEnts` are that
bucket's leaves' entries in order (no duplicates, keys strictly sorted by `treeKeys`). Used by U6
(the cursor specs' positions: `curAt` over `bktEnts`) and U10 (`freepages`' walk). -/
theorem bktEnts_treeEntries (C : CommitSt) (hok : treeOK C) (n : GoString) (m : BktData)
    (hn : treeData C !! n = some m) :
    ∃ v, (n, v) ∈ treeEntries C.pages C.root ∧ m = bktOfPage C.pages v ∧
      bktEnts m = bktEntries C.pages v := by
  sorry

end data

end bbolt
end EtcdGrove
end Perennial
