/-
The writer's heap, read (U8, `notes/bbolt-proof-plan.md`): a node's struct out of `wtxHeap` at
any fraction (live or dead), and the lookup of a bucket's node among the heap's objects.

`wtxHeap_objsDisj`: `wtxHeap`'s `heapOK` holds `objsDisj` (the shared fix of 2026-11-04).
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

omit hos in
/-- The heap's objects are disjoint (`heapOK`). -/
theorem wtxHeap_objsDisj (tx : Loc) (dq : DFrac) (X : WX) :
    wtxHeap (GF := GF) tx dq X ⊢ ⌜objsDisj X.t⌝ := by
  unfold wtxHeap
  iintro ⟨%H, -⟩
  ipureintro; exact H.2.1

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

omit hos in
/-- **An object, out and back unchanged** (its liveness as the heap has it). -/
theorem wtxHeap_obj_acc (tx : Loc) (dq : DFrac) (X : WX) (l : Loc) (o : WObj)
    (ho : X.t.objs !! l = some o) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v l dq (decide (l ∈ X.live)) o ∗
      (objOwn X.v l dq (decide (l ∈ X.live)) o -∗ wtxHeap tx dq X) := by
  unfold wtxHeap
  iintro ⟨%Hrl, Hf, Hrf, Hm⟩
  icases (BigSepM.bigSepM_lookup_acc ho).1 $$ Hm with ⟨Ho, Hback⟩
  iframe Ho
  iintro Ho
  iframe
  isplitr
  · ipureintro; exact Hrl
  iapply Hback
  iexact Ho

/-- **A live node of a bucket, out and back unchanged** (over `wtxHeap_objsDisj`). -/
theorem wtxHeap_live_node_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (n : Loc)
    (r : NRec) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r) (hl : n ∈ X.live) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v n dq true (.node bl r) ∗
      (objOwn X.v n dq true (.node bl r) -∗ wtxHeap tx dq X) := by
  iintro H
  ihave %Ho := wtxHeap_objs_node tx dq X bl B n r hb hr $$ H
  have e : decide (n ∈ X.live) = true := decide_eq_true hl
  have := wtxHeap_obj_acc (GF := GF) tx dq X n (.node bl r) Ho
  rw [e] at this
  iapply this $$ H

end heap

end bbolt
end EtcdGrove
end Perennial
