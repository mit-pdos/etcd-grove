/-
The writer's page tokens (U0a of `notes/bbolt-proof-plan.md`; design §3.12), ported from
`old/bbolt/.../WriteTxShape.lean` over `WX`: `txShape`, `bktToks`, `nodeToks`.

The transaction owns a ghost map (name `γ`, `TxNames.pg`) whose keys are page ids: one exclusive
token `id ↪[γ] ()` per page of the base view (and, during `Commit`, per page it allocated). Every
token sits with exactly one position of the logical tree, so a tree assembled from separately
held parts shares no page by separation alone. The positions of a bucket `B` (`bktToks`): without
a materialized root, its whole tree but the nested buckets it opened; otherwise each node: its own
page and, a branch, each child it has not materialized (that child's subtree), or, a leaf, each
nested bucket stored in pages that `B` has not opened (that bucket's tree). The pure parts of the
old `txShape` (`bktKeys`, `bktNested`, `txPg`) are in `wOK` (`Model/Wtx.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WtxHeap
public import Perennial.Ghost.GhostMap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section xhas
variable [GooseExts]

/-- Page `id` is a page of the tree under `root`, but for the nested buckets whose key `op` holds
(and their trees). -/
inductive xHas (pages : Pages) (op : List w8 → Prop) : Nat → Nat → Prop
  | root (root : Nat) (pg : List w8) : pages !! root = some pg → xHas pages op root root
  | child (root : Nat) (pg : List w8) (i id : Nat) :
      pages !! root = some pg → pageFlags pg = branchPageFlag → i < pageCount pg →
      xHas pages op (branchPgid pg i) id → xHas pages op root id
  | bucket (root : Nat) (pg : List w8) (i id : Nat) :
      pages !! root = some pg → pageFlags pg = leafPageFlag → i < pageCount pg →
      leafFlags pg i % 2 = bucketLeafFlag → ¬ op (leafKey pg i) →
      bucketHas pages (leafValue pg i) id → xHas pages op root id

open Classical in
/-- The pages `xHas` reaches. -/
def xPages (pages : Pages) (op : List w8 → Prop) (c : Nat) : Pages :=
  GMap.filter (fun id _ => decide (xHas pages op c id)) pages

end xhas

section toks
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The tokens of the pages `P`. -/
def pgToks (γ : GName) (P : Pages) : IProp GF := iprop([∗map] id ↦ _pg ∈ P, id ↪[γ] ())

open Classical in
/-- The tokens of a node's positions (see the module doc). -/
def nodeToks (γ : GName) (v : View) (B : BRec) (r : NRec) : IProp GF :=
  iprop((if r.nv.pgid' = W64 0 then emp else
      pgToks γ (GMap.filter (fun id _ => decide (id = r.nv.pgid'.toNat)) v.pages)) ∗
    [∗list] w ∈ r.ws,
      if r.nv.isLeaf' = true then
        (if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
          pgToks γ (treePages v.pages (inBucketRoot w.value)) else emp)
      else (if B.nm !! w.pgid = none then pgToks γ (xPages v.pages (opened B) w.pgid.toNat)
        else emp))

/-- The tokens of a bucket's positions (see the module doc). -/
def bktToks (γ : GName) (v : View) (B : BRec) : IProp GF :=
  if B.bv.rootNode' = null then
    (if B.ib.root' = W64 0 then iprop(emp)
     else pgToks γ (xPages v.pages (opened B) B.ib.root'.toNat))
  else iprop([∗map] _l ↦ r ∈ B.ns, nodeToks γ v B r)

/-- **The writer's page tokens**: the authority knows exactly the base view's page ids (and the
pages allocated during `Commit`, `extra`), and every token sits with its position. -/
def txShape (γ : GName) (X : WX) (extra : GMap Nat Unit) : IProp GF :=
  iprop(∃ M : GMap Nat Unit, ghostMapAuth γ 1 M ∗
    ⌜∀ id, (M !! id).isSome ↔ ((X.v.pages !! id).isSome ∨ (extra !! id).isSome)⌝ ∗
    ([∗map] _bl ↦ B ∈ X.t.bs, bktToks γ X.v B) ∗ pgToks γ (extra.fmap fun _ => ([] : List w8)))

end toks

end bbolt
end EtcdGrove
end Perennial
