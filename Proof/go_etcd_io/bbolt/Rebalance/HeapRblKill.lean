/-
A node of a bucket goes dead in the writer's heap (U8b, `node.rebalance`: a removed leaf, a
merged right sibling, a collapsed root's child): `WX.kill`, the object kept (now dead, its
facts dropped: `objOwn_weaken`), the bucket's record without the node.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.HeapRbl
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSDefs

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
/-- **A node goes dead** (`WX.kill`): the bucket's record `B'` is `B` without the node. -/
theorem wtxHeap_kill_node (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B B' : BRec) (n : Loc)
    (rn : NRec) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (h1 : B'.bv = B.bv) (h2 : B'.ib = B.ib) (h3 : B'.nm = B.nm) (h4 : B'.bm = B.bm)
    (h5 : B'.ipg = B.ipg) (h6 : B'.isrc = B.isrc) (h7 : B'.pst = B.pst)
    (hns : B'.ns = GMap.delete n B.ns) :
    wtxHeap (GF := GF) tx dq X ⊢ wtxHeap tx dq (X.kill bl B' n rn) := by
  iintro H
  ihave %Hok := wtxHeap_heapOK tx dq X $$ H
  have Hd := Hok.2.1
  have hnb : n ≠ bl := by
    intro h; have := (Hd bl B hb n (by simp [hr])).1; rw [h, hb] at this; cases this
  have Hon := objs_node X.t bl B n rn Hd hb hr
  have Hob := objs_bkt X.t bl B Hd hb
  have ho : ∀ l ∈ [n, bl], X.t.objs !! l =
      some ((fun l => if l = n then WObj.node bl rn else WObj.bkt B) l) := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hl
    rcases hl with rfl | rfl
    · simp [Hon]
    · simp [Hob, Ne.symm hnb]
  -- the new transaction's facts
  let T' : WTx := { X.t with bs := X.t.bs.insert bl B', dead := X.t.dead.insert n (.node bl rn) }
  have hT' : (X.kill bl B' n rn).t = T' := rfl
  have hbs' : ∀ c, T'.bs !! c = if c = bl then some B' else X.t.bs !! c := by
    intro c
    show (X.t.bs.insert bl B') !! c = _
    split
    · rename_i h; subst h; exact GMap.lookup_insert _ _ _
    · exact GMap.lookup_insert_ne _ _ (Ne.symm ‹_›)
  have hdom : ∀ c, (T'.bs !! c).isSome = (X.t.bs !! c).isSome := by
    intro c; rw [hbs']; split
    · rename_i h; subst h; rw [hb]; rfl
    · rfl
  have hns' : ∀ k, B'.ns !! k = if k = n then none else B.ns !! k := by
    intro k; rw [hns]; split
    · rename_i h; subst h; exact GMap.lookup_delete _ _
    · exact GMap.lookup_delete_ne _ (Ne.symm ‹_›)
  have hsub : ∀ c C C' k, X.t.bs !! c = some C → T'.bs !! c = some C' → (C'.ns !! k).isSome →
      (C.ns !! k).isSome := by
    intro c C C' k hc hc' hk
    rw [hbs'] at hc'
    split at hc'
    · rename_i h; subst h; cases hc'; rw [hb] at hc; cases hc
      rw [hns'] at hk; split at hk
      · cases hk
      · exact hk
    · rw [hc] at hc'; cases hc'; exact hk
  have Hd' : objsDisj T' := objsDisj_sub X.t T' Hd hdom hsub
  have hagree := objs_agree X.t T' [n, bl] Hd Hd' hdom
    (fun c hc => by
      rw [hbs']; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hc
      rw [if_neg hc.2])
    (fun c C C' k hc hc' hk => by
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hk
      rw [hbs'] at hc'
      split at hc'
      · rename_i h; subst h; cases hc'; rw [hb] at hc; cases hc
        rw [hns', if_neg hk.1]
      · rw [hc] at hc'; cases hc'; rfl)
    (fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hk
      show (X.t.dead.insert n _) !! k = _
      exact GMap.lookup_insert_ne _ _ (Ne.symm hk.1))
  have Hon' : T'.objs !! n = some (.node bl rn) := by
    rw [objs_other T' n]
    · show (X.t.dead.insert n _) !! n = _; exact GMap.lookup_insert _ _ _
    · intro c C' hc'
      obtain ⟨C, hc⟩ : ∃ C, X.t.bs !! c = some C := by
        have := hdom c; rw [hc'] at this; exact Option.isSome_iff_exists.1 this.symm
      refine ⟨fun h => ?_, ?_⟩
      · rw [← h] at hc; have := (Hd bl B hb n (by simp [hr])).1; rw [hc] at this; cases this
      · rw [hbs'] at hc'
        split at hc'
        · rename_i h; subst h; cases hc'; rw [hns', if_pos rfl]
        · rename_i hcb
          have hcC : X.t.bs !! c = some C' := hc'
          exact (Hd bl B hb n (by simp [hr])).2 c C' hcC hcb
  have Hob' : T'.objs !! bl = some (.bkt B') := objs_bkt T' bl B' Hd' (by rw [hbs', if_pos rfl])
  icases wtxHeap_reshape tx dq X [n, bl] _ (by simp [hnb]) ho $$ H with ⟨⟨Hn, Hb, -⟩, Hf, Hrf, Hback⟩
  iapply Hback $$ %(X.kill bl B' n rn)
    %(fun l => if l = n then WObj.node bl rn else WObj.bkt B') [] [Hn Hb] [Hf] [Hrf]
  · ipureintro
    refine ⟨?_, rfl, ?_, ?_⟩
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hl
      rw [hT']
      rcases hl with rfl | rfl
      · simp only [ite_true]; exact Hon'
      · simp only [if_neg (Ne.symm hnb)]; exact Hob'
    · intro k hk
      refine ⟨by rw [hT']; exact hagree k hk, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hk
      show k ∈ X.live.delete n ↔ k ∈ X.live
      simp only [GMap.mem_iff, GMap.lookup_delete_ne _ (Ne.symm hk.1)]
    · refine heapOK_of tx X _ Hok rfl Hd' ?_ ?_ rfl ?_
      · intro c C' hc'
        rw [hT', hbs'] at hc'
        split at hc'
        · rename_i h; subst h; cases hc'; exact ⟨B, hb, by rw [h1]⟩
        · exact ⟨C', hc', rfl⟩
      · intro c C' k rk hc' hk
        rw [hT', hbs'] at hc'
        split at hc'
        · rename_i h; subst h; cases hc'
          rw [hns'] at hk; split at hk
          · cases hk
          · exact Hok.2.2.2.1 c B k rk hb hk
        · exact Hok.2.2.2.1 c C' k rk hc' hk
      · intro k hk
        rw [hT']
        by_cases hkL : k ∈ [n, bl]
        · simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hkL
          rcases hkL with rfl | rfl
          · rw [Hon']; rfl
          · rw [Hob']; rfl
        · rw [hagree k hkL]; exact hk
  · isplitl [Hn]
    · simp only [ite_true]
      iapply objOwn_weaken X.v n dq _ _ _ ?_ $$ Hn
      intro h
      simp only [decide_eq_true_eq] at h
      exact absurd h (by show ¬ (n ∈ X.live.delete n); simp [GMap.mem_iff])
    isplitl [Hb]
    · simp only [if_neg (Ne.symm hnb)]
      have hbl' : decide (bl ∈ (X.kill bl B' n rn).live) = decide (bl ∈ X.live) := by
        apply decide_eq_decide.2
        show bl ∈ X.live.delete n ↔ bl ∈ X.live
        simp only [GMap.mem_iff, GMap.lookup_delete_ne _ hnb]
      rw [hbl', objOwn_bkt_eq _ _ _ _ B B' h1 h2 h3 h4 h5 h6 h7]
      iexact Hb
    iempintro
  · rw [txFields_congr tx dq (X.kill bl B' n rn) X rfl rfl rfl rfl]; iexact Hf
  · iexact Hrf

end heap

end bbolt
end EtcdGrove
end Perennial
