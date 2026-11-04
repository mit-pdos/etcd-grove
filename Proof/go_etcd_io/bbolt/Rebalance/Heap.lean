/-
The writer's heap, read (U8, `notes/bbolt-proof-plan.md`): a node's struct out of `wtxHeap` at
any fraction (live or dead), and the lookup of a bucket's node among the heap's objects.

`wtxHeap_objsDisj` is **not provable from the current definitions**: `wtxHeap` holds no fact
that the buckets' node locations are disjoint (`objsDisj`), and `WTx.objs` (a map) keeps one of
two records at a shared location, so `B.ns !! n = some r` (what the frozen specs of `node.root`,
`childAt`, the siblings and `node.free` give) does not give `X.t.objs !! n = some (.node bl r)`
(what `wtxHeap_node_acc` and the reads here need). It is the `sorry` those proofs rest on until
`wtxHeap` carries `⌜objsDisj X.t⌝` (a shared definition: reported, not changed here; every
operation adding an object adds a fresh location, `nodeAdded`'s `(X.t.objs !! l).isNone`, so it is
kept).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Rebalance.Objs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **PENDING a shared fix** (see the module doc): the heap's objects are disjoint. -/
theorem wtxHeap_objsDisj (tx : Loc) (dq : DFrac) (X : WX) :
    wtxHeap (GF := GF) tx dq X ⊢ ⌜objsDisj X.t⌝ := by
  sorry

/-- A node of a bucket of the heap is its object. -/
theorem wtxHeap_objs_node (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (n : Loc)
    (r : NRec) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r) :
    wtxHeap (GF := GF) tx dq X ⊢ ⌜X.t.objs !! n = some (.node bl r)⌝ := by
  iintro H
  ihave %Hd := wtxHeap_objsDisj tx dq X $$ H
  ipureintro
  exact objs_node X.t bl B n r Hd hb hr

omit hos in
/-- **A node's struct, read** out of the heap at its fraction (live or dead), and back. -/
theorem wtxHeap_node_ptr_acc (tx : Loc) (dq : DFrac) (X : WX) (bl l : Loc) (r : NRec)
    (ho : X.t.objs !! l = some (.node bl r)) :
    wtxHeap (GF := GF) tx dq X ⊢ l ↦{dq} r.nv ∗ (l ↦{dq} r.nv -∗ wtxHeap tx dq X) := by
  unfold wtxHeap
  iintro ⟨%Hrl, Hf, Hrf, Hm⟩
  icases (BigSepM.bigSepM_lookup_acc ho).1 $$ Hm with ⟨Ho, Hback⟩
  unfold objOwn
  icases Ho with ⟨Hl, Hrest⟩
  iframe Hl
  iintro Hl
  iframe
  isplitr
  · ipureintro; exact Hrl
  iapply Hback
  dsimp only
  iframe

end heap

end bbolt
end EtcdGrove
end Perennial
