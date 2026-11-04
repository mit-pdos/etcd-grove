/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`): **a piece's node and
its page buffer, out of the writer's heap and back** (what `node.write(p)` writes; with the transaction's meta, what the page id's check reads): the buffers'
bytes by page id (`bufs_acc`), and a node's object with a buffer (`wtxHeap_node_buf_acc`, back with
a new record and new bytes: `X.setNode`, `X.setBuf`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesStep
public import Proof.go_etcd_io.bbolt.Rebalance.HeapRbl
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillHeap

@[expose] public section

noncomputable section

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

omit hos [GooseSemantics] go_gctx sem in
/-- **A buffer's bytes, out of the page cache's, and back with new bytes.** -/
theorem bufs_acc (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (dq : DFrac) (id : w64) (p : Loc)
    (bs : List w8) (hpm : pm !! id = some p) (hbs : bufs !! id = some bs) :
    ([∗map] id' ↦ pl ∈ pm, ∃ bs, ⌜bufs !! id' = some bs⌝ ∗ bytesPointsto (GF := GF) pl dq bs) ⊢
      bytesPointsto p dq bs ∗ (∀ bs', bytesPointsto p dq bs' -∗
        [∗map] id' ↦ pl ∈ pm, ∃ bs, ⌜(bufs.insert id bs') !! id' = some bs⌝ ∗
          bytesPointsto pl dq bs) := by
  iintro H
  icases (BigSepM.bigSepM_lookup_acc_impl hpm) $$ H with ⟨⟨%bs0, %Hb0, Hp⟩, Hback⟩
  rw [hbs] at Hb0
  cases Hb0
  iframe Hp
  iintro %bs' Hp
  iapply Hback
  · imodintro
    iintro %k %v %_ %Hne ⟨%b, %Hb, Hb⟩
    iexists b
    iframe Hb
    ipureintro
    rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne)]; exact Hb
  · iexists bs'
    iframe Hp
    ipureintro; exact GMap.lookup_insert _ _ _

omit hos in
theorem objOwn_bkt_ns (v : View) (l : Loc) (dq : DFrac) (b : Bool) (B : BRec)
    (ns : GMap Loc NRec) :
    objOwn (GF := GF) v l dq b (.bkt { B with ns := ns }) ⊣⊢ objOwn v l dq b (.bkt B) := by
  simp only [objOwn, pageOwn]; exact .rfl

omit hos in
/-- **A live node's object and a buffer, out of the heap, and back with a new record and new
bytes** (the record's parent not the node). -/
theorem wtxHeap_node_buf_acc (tx : Loc) (X : WX) (bl l : Loc) (r : NRec) (id : w64) (p : Loc)
    (bs : List w8) (hn : X.node bl l = some r) (hlv : l ∈ X.live) (hpm : X.t.pm !! id = some p)
    (hbs : X.t.bufs !! id = some bs) :
    wtxHeap (GF := GF) tx (DFrac.own 1) X ⊢ objOwn X.v l (DFrac.own 1) true (.node bl r) ∗
      bytesPointsto p (DFrac.own 1) bs ∗
      tx.[Tx, go!"meta"] ↦ X.t.t.meta' ∗ X.t.t.meta' ↦ X.t.mv ∗
      (∀ r' bs', ⌜r'.nv.parent' ≠ l⌝ -∗ objOwn X.v l (DFrac.own 1) true (.node bl r') -∗
        bytesPointsto p (DFrac.own 1) bs' -∗
        tx.[Tx, go!"meta"] ↦ X.t.t.meta' -∗ X.t.t.meta' ↦ X.t.mv -∗
        wtxHeap tx (DFrac.own 1) ((X.setNode bl l r').setBuf id bs')) := by
  obtain ⟨B, hb, hr⟩ := node_bs_of hn
  iintro H
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ H
  have Hd := Hok.2.1
  have ho := objs_node X.t bl B l r Hd hb hr
  have hob := bobjs_bkt X.t bl B hb
  icases wtxHeap_reshape tx (DFrac.own 1) X [l] (fun _ => .node bl r) [bl] (fun _ => B)
    (by simp) (by intro k hk; rw [List.mem_singleton.1 hk]; exact ho)
    (by simp) (by intro k hk; rw [List.mem_singleton.1 hk]; exact hob) $$ H
    with ⟨⟨Hl, -⟩, ⟨Hb, -⟩, Hf, Hrf, Hback⟩
  rw [decide_eq_true hlv]
  unfold txFields
  icases Hf with ⟨Hf1, Hf2, Hf3, Hf4, Hf5, Hf6, Hf7, Hf8, Hbufs⟩
  icases bufs_acc X.t.pm X.t.bufs (DFrac.own 1) id p bs hpm hbs $$ Hbufs with ⟨Hp, Hbufs⟩
  iframe Hl Hp Hf3 Hf7
  iintro %r' %bs' %Hpar Hl Hp Hf3 Hf7
  ihave Hbufs := Hbufs $$ %bs' Hp
  have hX : (X.setNode bl l r').setBuf id bs' =
      { X with t := { X.t.setNodeT bl l B r' with bufs := X.t.bufs.insert id bs' } } := by
    rw [setNode_eq X bl l B r' hb]; rfl
  rw [hX]
  have hobj := objs_setNodeT X.t bl l B r r' Hd hb hr
  iapply Hback $$ %{ X with t := { X.t.setNodeT bl l B r' with bufs := X.t.bufs.insert id bs' } }
    %(fun _ => .node bl r') %(fun _ => { B with ns := B.ns.insert l r' }) [] [Hl] [Hb]
    [Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hbufs] Hrf
  · ipureintro
    have hok' := heapOK_setNode tx X bl B l r r' Hok hb hr Hpar
    refine ⟨?_, ?_, rfl, ?_, ?_, hok'⟩
    · intro k hk
      rw [List.mem_singleton.1 hk]
      show (X.t.setNodeT bl l B r').objs !! l = _
      rw [hobj]; exact GMap.lookup_insert _ _ _
    · intro k hk
      rw [List.mem_singleton.1 hk]
      show (X.t.setNodeT bl l B r').bobjs !! bl = _
      rw [bobjs_setNodeT]; exact GMap.lookup_insert _ _ _
    · intro k hk
      refine ⟨?_, Iff.rfl⟩
      show (X.t.setNodeT bl l B r').objs !! k = _
      rw [hobj, GMap.lookup_insert_ne _ _ (fun e => hk (by simp [e]))]
    · intro k hk
      refine ⟨?_, Iff.rfl⟩
      show (X.t.setNodeT bl l B r').bobjs !! k = _
      rw [bobjs_setNodeT, GMap.lookup_insert_ne _ _ (fun e => hk (by simp [e]))]
  · iapply BigSepL.bigSepL_cons.2
    isplitl
    · simp only [decide_eq_true hlv]; iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · iapply BigSepL.bigSepL_cons.2
    isplitl
    · iapply (objOwn_bkt_ns _ _ _ _ _ _).2; iexact Hb
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · iframe

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
