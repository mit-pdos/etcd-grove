/-
U7o (`notes/bbolt-proof-plan.md`): **`DeleteBucket`'s heap steps** on the writer's records:
- `wtxW_bm_acc`: a live bucket's `buckets` field and cache map, out of `wtxW` and back with a new
  map (`delete(b.buckets, key)` on the root bucket);
- `wtxW_dead_nil`: a dead bucket's `nodes` and `rootNode` fields, out and back nil
  (`child.nodes = nil`, `child.rootNode = nil`), its record then `deadRec`: no node, no node cache.
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktKill

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- A dead bucket's record after `child.nodes = nil` and `child.rootNode = nil`: no nodes, no
node cache. -/
def deadRec (C : BRec) : BRec :=
  { C with ns := ∅, nm := ∅, bv := { C.bv with nodes' := null, rootNode' := null } }

theorem deadRec_root (C : BRec) : (deadRec C).ib.root' = C.ib.root' := rfl
theorem deadRec_tx (C : BRec) : (deadRec C).bv.tx' = C.bv.tx' := rfl
theorem deadRec_page (C : BRec) : (deadRec C).bv.page' = C.bv.page' := rfl
theorem deadRec_nodes (C : BRec) : (deadRec C).bv.nodes' = null := rfl

end pure

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A live bucket's cache of nested buckets**, out of `wtxW` and back with a new map. -/
theorem wtxW_bm_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) (hl : bl ∈ X.liveB) :
    wtxW (GF := GF) K tx r m X ⊢
      bl.[Bucket, go!"buckets"] ↦ B.bv.buckets' ∗ B.bv.buckets' ↦$ B.bm ∗
      (∀ bm, bl.[Bucket, go!"buckets"] ↦ B.bv.buckets' -∗ B.bv.buckets' ↦$ bm -∗
        wtxW K tx r m (X.setBkt bl { B with bm := bm })) := by
  iintro Hw
  icases wtxW_open K tx r m X $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hwback⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  icases wtxHeap_bkt_acc tx (DFrac.own 1) X bl B hb hl $$ Hh with ⟨Ho, Hhb⟩
  unfold objOwn
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe H3 H9
  iintro %bm H3 H9
  ihave Hh := Hhb $$ %{ B with bm := bm } [] [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
  · ipureintro; exact Hok.2.2.1 bl B hb
  · dsimp only
    iframe
  iapply Hwback $$ %(X.setBkt bl { B with bm := bm }) [] Hh Hv Hst
  ipureintro; exact ⟨rfl, rfl, rfl⟩

/-- **A dead bucket's node caches set nil** (`child.nodes = nil`, `child.rootNode = nil`). -/
theorem wtxW_dead_nil (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hbs : X.t.bs !! bl = none) (hd : X.t.deadB !! bl = some B) (hl : bl ∉ X.liveB) :
    wtxW (GF := GF) K tx r m X ⊢
      bl.[Bucket, go!"nodes"] ↦ B.bv.nodes' ∗ bl.[Bucket, go!"rootNode"] ↦ B.bv.rootNode' ∗
      (bl.[Bucket, go!"nodes"] ↦ null -∗ bl.[Bucket, go!"rootNode"] ↦ null -∗
        wtxW K tx r m (X.setDead bl (deadRec B))) := by
  iintro Hw
  icases wtxW_dead_acc K tx r m X bl B hbs hd $$ Hw with ⟨Ho, Hback⟩
  rw [decide_eq_false hl]
  unfold objOwn
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, -, H9, -⟩
  iframe H5 H6
  iintro H6 H5
  iapply Hback $$ %(deadRec B)
  unfold deadRec
  dsimp only
  iframe
  simp only [↓reduceIte, Bool.false_eq_true]
  ipureintro; trivial

end heap

end Write

end bbolt
end EtcdGrove
end Perennial
