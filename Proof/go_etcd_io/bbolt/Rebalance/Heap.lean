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
  icases objOwn_node_ptr_acc X.v l dq _ bl r $$ Ho with ⟨Hl, Hob⟩
  iframe Hl
  iintro Hl
  iframe
  isplitr
  · ipureintro; exact Hrl
  iapply Hback
  iapply Hob
  iexact Hl

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

omit hos in
/-- **Two distinct objects, out and back unchanged.** -/
theorem wtxHeap_two_acc (tx : Loc) (dq : DFrac) (X : WX) (a b : Loc) (oa ob : WObj)
    (hoa : X.t.objs !! a = some oa) (hob : X.t.objs !! b = some ob) (hne : a ≠ b) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v a dq (decide (a ∈ X.live)) oa ∗
      objOwn X.v b dq (decide (b ∈ X.live)) ob ∗
      (objOwn X.v a dq (decide (a ∈ X.live)) oa -∗ objOwn X.v b dq (decide (b ∈ X.live)) ob -∗
        wtxHeap tx dq X) := by
  unfold wtxHeap
  iintro ⟨%Hrl, Hf, Hrf, Hm⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) hoa).1 $$ Hm with ⟨Ha, Hm⟩
  have hob' : Iris.Std.get? (Iris.Std.delete X.t.objs a) b = some ob := by
    rw [Iris.Std.LawfulPartialMap.get?_delete_ne hne]; exact hob
  icases (BigSepM.bigSepM_lookup_acc hob').1 $$ Hm with ⟨Hb, Hback⟩
  iframe Ha Hb
  iintro Ha Hb
  iframe
  isplitr
  · ipureintro; exact Hrl
  iapply (BigSepM.bigSepM_delete (M := GMap Loc) hoa).2
  iframe Ha
  iapply Hback
  iexact Hb

/-- **Two distinct live nodes of a bucket, out and back unchanged.** -/
theorem wtxHeap_two_nodes_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec)
    (a b : Loc) (ra rb : NRec) (hb : X.t.bs !! bl = some B) (hra : B.ns !! a = some ra)
    (hrb : B.ns !! b = some rb) (hla : a ∈ X.live) (hlb : b ∈ X.live) (hne : a ≠ b) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v a dq true (.node bl ra) ∗
      objOwn X.v b dq true (.node bl rb) ∗
      (objOwn X.v a dq true (.node bl ra) -∗ objOwn X.v b dq true (.node bl rb) -∗
        wtxHeap tx dq X) := by
  iintro H
  ihave %Hoa := wtxHeap_objs_node tx dq X bl B a ra hb hra $$ H
  ihave %Hob := wtxHeap_objs_node tx dq X bl B b rb hb hrb $$ H
  have := wtxHeap_two_acc (GF := GF) tx dq X a b _ _ Hoa Hob hne
  rw [decide_eq_true hla, decide_eq_true hlb] at this
  iapply this $$ H

omit hos in
/-- A big separating conjunction over a map with one entry replaced by one of the same
resource. -/
theorem bigSepM_insert_same {Φ : Loc → WObj → IProp GF} (m : GMap Loc WObj) (k : Loc)
    (v v' : WObj) (hk : m !! k = some v) (heq : Φ k v' = Φ k v) :
    ([∗map] l ↦ o ∈ m.insert k v', Φ l o) ⊣⊢ [∗map] l ↦ o ∈ m, Φ l o := by
  refine (BigSepM.bigSepM_insert_delete (M := GMap Loc)).trans ?_
  rw [heq]
  exact (BigSepM.bigSepM_delete (M := GMap Loc) hk).symm

omit hos in
theorem setNode_eq (X : WX) (bl n : Loc) (B : BRec) (r' : NRec) (hb : X.t.bs !! bl = some B) :
    X.setNode bl n r' = { X with t := X.t.setNodeT bl n B r' } := by
  unfold WX.setNode WX.setBkt WTx.setNodeT
  rw [hb]

omit hos in
/-- **A node's object, out, and back with a new record** (live or dead; its parent not
itself): the heap of `X.setNode`. -/
theorem wtxHeap_setNode (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (n : Loc)
    (r : NRec) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v n dq (decide (n ∈ X.live)) (.node bl r) ∗
      (∀ r', ⌜r'.nv.parent' ≠ n⌝ -∗ objOwn X.v n dq (decide (n ∈ X.live)) (.node bl r') -∗
        wtxHeap tx dq (X.setNode bl n r')) := by
  unfold wtxHeap
  iintro ⟨%Hok, Hf, Hrf, Hm⟩
  have Hd := Hok.2.1
  have Ho := objs_node X.t bl B n r Hd hb hr
  have hnb : n ≠ bl := by
    intro h; have := (Hd bl B hb n (by simp [hr])).1; rw [h, hb] at this; cases this
  icases (BigSepM.bigSepM_delete (M := GMap Loc) Ho).1 $$ Hm with ⟨Hn, Hm⟩
  iframe Hn
  iintro %r' %Hpar Hn
  rw [setNode_eq X bl n B r' hb]
  isplitr
  · ipureintro
    refine ⟨Hok.1, objsDisj_setNodeT X.t bl n B r r' Hd hb hr, ?_, ?_⟩
    · intro c C hc
      by_cases hcb : c = bl
      · subst hcb
        simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc
        subst hc; exact Hok.2.2.1 c B hb
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
        exact Hok.2.2.1 c C hc
    · intro c C k rk hc hk
      by_cases hcb : c = bl
      · subst hcb
        simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc
        subst hc
        by_cases hkn : k = n
        · subst hkn
          simp only [GMap.lookup_insert, Option.some.injEq] at hk
          subst hk; exact Hpar
        · simp only [GMap.lookup_insert_ne _ _ (Ne.symm hkn)] at hk
          exact Hok.2.2.2 c B k rk hb hk
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
        exact Hok.2.2.2 c C k rk hc hk
  isplitl [Hf]
  · unfold txFields; simp only [WTx.setNodeT]; iexact Hf
  iframe
  rw [objs_setNodeT X.t bl n B r r' Hd hb hr]
  have hlk : (X.t.objs.insert n (.node bl r')) !! bl = some (.bkt B) := by
    rw [GMap.lookup_insert_ne _ _ hnb]; exact objs_bkt X.t bl B Hd hb
  dsimp only
  iapply (bigSepM_insert_same (Φ := fun l o => objOwn (GF := GF) X.v l dq (decide (l ∈ X.live)) o)
    _ bl _ (.bkt { B with ns := B.ns.insert n r' }) hlk (by simp only [objOwn, pageOwn])).2
  iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc)).2
  iframe

omit hos in
/-- The same, with the node's bucket and the transaction's fields out too. -/
theorem wtxHeap_setNode_bkt (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (n : Loc)
    (r : NRec) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v n dq (decide (n ∈ X.live)) (.node bl r) ∗
      objOwn X.v bl dq (decide (bl ∈ X.live)) (.bkt B) ∗ txFields tx dq X ∗
      (∀ r', ⌜r'.nv.parent' ≠ n⌝ -∗ objOwn X.v n dq (decide (n ∈ X.live)) (.node bl r') -∗
        objOwn X.v bl dq (decide (bl ∈ X.live)) (.bkt B) -∗ txFields tx dq X -∗
        wtxHeap tx dq (X.setNode bl n r')) := by
  unfold wtxHeap
  iintro ⟨%Hok, Hf, Hrf, Hm⟩
  have Hd := Hok.2.1
  have Ho := objs_node X.t bl B n r Hd hb hr
  have hnb : n ≠ bl := by
    intro h; have := (Hd bl B hb n (by simp [hr])).1; rw [h, hb] at this; cases this
  icases (BigSepM.bigSepM_delete (M := GMap Loc) Ho).1 $$ Hm with ⟨Hn, Hm⟩
  have hob' : Iris.Std.get? (Iris.Std.delete X.t.objs n) bl = some (.bkt B) := by
    rw [Iris.Std.LawfulPartialMap.get?_delete_ne hnb]; exact objs_bkt X.t bl B Hd hb
  icases (BigSepM.bigSepM_lookup_acc hob').1 $$ Hm with ⟨Hb, Hmb⟩
  iframe Hn Hb Hf
  iintro %r' %Hpar Hn Hb Hf
  ihave Hm := Hmb $$ Hb
  rw [setNode_eq X bl n B r' hb]
  isplitr
  · ipureintro
    refine ⟨Hok.1, objsDisj_setNodeT X.t bl n B r r' Hd hb hr, ?_, ?_⟩
    · intro c C hc
      by_cases hcb : c = bl
      · subst hcb
        simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc
        subst hc; exact Hok.2.2.1 c B hb
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
        exact Hok.2.2.1 c C hc
    · intro c C k rk hc hk
      by_cases hcb : c = bl
      · subst hcb
        simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc
        subst hc
        by_cases hkn : k = n
        · subst hkn
          simp only [GMap.lookup_insert, Option.some.injEq] at hk
          subst hk; exact Hpar
        · simp only [GMap.lookup_insert_ne _ _ (Ne.symm hkn)] at hk
          exact Hok.2.2.2 c B k rk hb hk
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
        exact Hok.2.2.2 c C k rk hc hk
  isplitl [Hf]
  · unfold txFields; simp only [WTx.setNodeT]; iexact Hf
  iframe
  rw [objs_setNodeT X.t bl n B r r' Hd hb hr]
  have hlk : (X.t.objs.insert n (.node bl r')) !! bl = some (.bkt B) := by
    rw [GMap.lookup_insert_ne _ _ hnb]; exact objs_bkt X.t bl B Hd hb
  dsimp only
  iapply (bigSepM_insert_same (Φ := fun l o => objOwn (GF := GF) X.v l dq (decide (l ∈ X.live)) o)
    _ bl _ (.bkt { B with ns := B.ns.insert n r' }) hlk (by simp only [objOwn, pageOwn])).2
  iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc)).2
  iframe

omit hos in
/-- A node's struct, out of its object, and back with a new page id. -/
theorem objOwn_node_pgid_upd (v : View) (l : Loc) (dq : DFrac) (b : Bool) (bl : Loc) (r : NRec) :
    objOwn (GF := GF) v l dq b (.node bl r) ⊢
      l ↦{dq} r.nv ∗ (∀ p : w64, l ↦{dq} ({ r.nv with pgid' := p } : node) -∗
        objOwn v l dq b (.node bl { r with nv := { r.nv with pgid' := p } })) := by
  cases b with
  | true =>
    unfold objOwn
    dsimp only
    iintro ⟨Hl, Hr⟩
    iframe Hl
    iintro %p Hl
    iframe
  | false =>
    unfold objOwn
    dsimp only
    iintro Hl
    iframe Hl
    iintro %p Hl
    iexact Hl

omit hos in
/-- **What `node.free` reads**: the node's struct, its bucket's object and the transaction's
fields, and back. -/
theorem wtxHeap_free_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (n : Loc)
    (r : NRec) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r) :
    wtxHeap (GF := GF) tx dq X ⊢ n ↦{dq} r.nv ∗
      objOwn X.v bl dq (decide (bl ∈ X.live)) (.bkt B) ∗ txFields tx dq X ∗
      (n ↦{dq} r.nv -∗ objOwn X.v bl dq (decide (bl ∈ X.live)) (.bkt B) -∗ txFields tx dq X -∗
        wtxHeap tx dq X) := by
  iintro H
  ihave %Hok := wtxHeap_heapOK tx dq X $$ H
  have Hd := Hok.2.1
  have Hon := objs_node X.t bl B n r Hd hb hr
  have Hob := objs_bkt X.t bl B Hd hb
  have hnb : n ≠ bl := by
    intro h; have := (Hd bl B hb n (by simp [hr])).1; rw [h, hb] at this; cases this
  unfold wtxHeap
  icases H with ⟨%Hok', Hf, Hrf, Hm⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) Hon).1 $$ Hm with ⟨Hn, Hm⟩
  have hob' : Iris.Std.get? (Iris.Std.delete X.t.objs n) bl = some (.bkt B) := by
    rw [Iris.Std.LawfulPartialMap.get?_delete_ne hnb]; exact Hob
  icases (BigSepM.bigSepM_lookup_acc hob').1 $$ Hm with ⟨Hb, Hback⟩
  icases objOwn_node_ptr_acc X.v n dq _ bl r $$ Hn with ⟨Hn, Hnb⟩
  iframe Hn Hb Hf
  iintro Hn Hb Hf
  iframe
  isplitr
  · ipureintro; exact Hok'
  iapply (BigSepM.bigSepM_delete (M := GMap Loc) Hon).2
  isplitl [Hn Hnb]
  · iapply Hnb $$ Hn
  iapply Hback
  iexact Hb

end heap

end bbolt
end EtcdGrove
end Perennial
