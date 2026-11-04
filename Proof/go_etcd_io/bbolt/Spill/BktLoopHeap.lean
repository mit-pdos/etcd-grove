/-
`Bucket.spill`'s root loop (U9q, `notes/bbolt-proof-plan.md`): **the heap accessors** the loop body
uses: a child bucket's object with the transaction's `db` field and the page size
(`b.inlineable()` without a root node), and with its root node's object and the view's cells too
(`b.inlineable()`, `b.write()`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesOne

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A bucket's object and a live node's object (of any bucket), out of the heap**, and back
unchanged. -/
theorem wtxHeap_bkt_node_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (c n : Loc)
    (C : BRec) (rn : NRec) (hb : X.t.bs !! bl = some B) (hc : X.t.bs !! c = some C)
    (hn : C.ns !! n = some rn) (hl : n ∈ X.live) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B) ∗
      objOwn X.v n dq true (.node c rn) ∗
      (objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B) -∗ objOwn X.v n dq true (.node c rn) -∗
        wtxHeap tx dq X) := by
  iintro H
  ihave %Ho := wtxHeap_objs_node tx dq X c C n rn hc hn $$ H
  unfold wtxHeap
  icases H with ⟨%Hrl, Hf, Hrf, Hm, Hbk⟩
  icases (BigSepM.bigSepM_lookup_acc (bobjs_bkt X.t bl B hb)).1 $$ Hbk with ⟨Hbo, Hbback⟩
  icases (BigSepM.bigSepM_lookup_acc Ho).1 $$ Hm with ⟨Hno, Hnback⟩
  rw [decide_eq_true hl]
  iframe Hbo Hno
  iintro Hbo Hno
  iframe
  isplitr
  · ipureintro; exact Hrl
  isplitl [Hnback Hno]
  · iapply Hnback; iexact Hno
  iapply Hbback; iexact Hbo

variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A live bucket's object, the transaction's `db` field and the page size, out of `wtxW`**, and
back. -/
theorem wtxW_bkt_db_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (c : Loc) (C : BRec)
    (hc : X.t.bs !! c = some C) (hcl : c ∈ X.liveB) :
    wtxW (GF := GF) K tx r m X ⊢ objOwn X.v c (DFrac.own 1) true (.bkt C) ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗ K.db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
      (objOwn X.v c (DFrac.own 1) true (.bkt C) -∗
        tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ wtxW K tx r m X) := by
  iintro Hw
  icases (wtxW_split K tx r m X).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
  unfold wtxCore
  icases Hc with ⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  ihave #Hps := isBoltCoreP_pageSize K.B K.N K.db K.p K.sp K.t0 $$ [Hcore]
  · unfold BC.core; iexact Hcore
  icases wtxHeap_bkt_obj_acc tx (DFrac.own 1) X c C (bobjs_bkt X.t c C hc) $$ Hh with ⟨Ho, Hback⟩
  rw [decide_eq_true hcl, Hr.1]
  iframe Ho Hdbf Hps
  iintro Ho Hdbf
  ihave Hh := Hback $$ Ho
  iapply (wtxW_split K tx r m X).2
  unfold wtxCore
  rw [← Hr.1]
  iframe; iframe #
  ipureintro; exact ⟨rfl, Hr.2⟩

/-- **A live bucket's object, a live node of it, the view's cells, the transaction's `db` field
and the page size, out of `wtxW`**, and back. -/
theorem wtxW_bkt_root_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (c : Loc) (C : BRec)
    (n : Loc) (rn : NRec) (hc : X.t.bs !! c = some C) (hcl : c ∈ X.liveB) (hn : C.ns !! n = some rn)
    (hl : n ∈ X.live) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜0 < X.v.base.addr⌝ ∗ objOwn X.v c (DFrac.own 1) true (.bkt C) ∗
      objOwn X.v n (DFrac.own 1) true (.node c rn) ∗ viewCells wq X.v ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗ K.db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
      (objOwn X.v c (DFrac.own 1) true (.bkt C) -∗ objOwn X.v n (DFrac.own 1) true (.node c rn) -∗
        viewCells wq X.v -∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ wtxW K tx r m X) := by
  iintro Hw
  icases (wtxW_split K tx r m X).1 $$ Hw with ⟨Hc, Hcells, ⟨%l, Hmf, %Hl⟩⟩
  ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  unfold wtxCore
  icases Hc with ⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  ihave #Hps := isBoltCoreP_pageSize K.B K.N K.db K.p K.sp K.t0 $$ [Hcore]
  · unfold BC.core; iexact Hcore
  icases wtxHeap_bkt_node_acc tx (DFrac.own 1) X c C c n C rn hc hc hn hl $$ Hh
    with ⟨Ho, Hno, Hback⟩
  rw [decide_eq_true hcl, Hr.1]
  iframe Ho Hno Hdbf Hps Hcells
  isplitr
  · ipureintro; exact Hnn
  iintro Ho Hno Hcells Hdbf
  rw [← decide_eq_true (p := c ∈ X.liveB) hcl]
  ihave Hh := Hback $$ Ho Hno
  iapply (wtxW_split K tx r m X).2
  unfold wtxCore
  rw [← Hr.1]
  iframe; iframe #
  isplitr
  · ipureintro; exact ⟨rfl, Hr.2⟩
  ipureintro; exact Hl

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
