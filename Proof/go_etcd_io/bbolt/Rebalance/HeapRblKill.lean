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
  have Hon := objs_node X.t bl B n rn Hd hb hr
  have Hob := bobjs_bkt X.t bl B hb
  -- the new transaction's facts
  let T' : WTx := { X.t with bs := X.t.bs.insert bl B', dead := X.t.dead.insert n (bl, rn) }
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
  have hagree := objs_agree X.t T' [n] Hd Hd' hdom
    (fun c C C' k hc hc' hk => by
      simp only [List.mem_singleton] at hk
      rw [hbs'] at hc'
      split at hc'
      · rename_i h; subst h; cases hc'; rw [hb] at hc; cases hc
        rw [hns', if_neg hk]
      · rw [hc] at hc'; cases hc'; rfl)
    (fun k hk => by
      simp only [List.mem_singleton] at hk
      show (X.t.dead.insert n _) !! k = _
      exact GMap.lookup_insert_ne _ _ (Ne.symm hk))
  have hagreeB := bobjs_agree X.t T' [bl]
    (fun c hc => by
      simp only [List.mem_singleton] at hc
      rw [hbs', if_neg hc])
    (fun k _ => rfl)
  have Hon' : T'.objs !! n = some (.node bl rn) := by
    rw [objs_other T' n]
    · show (X.t.dead.insert n (bl, rn)).fmap _ !! n = _
      simp [GMap.lookup_fmap, GMap.lookup_insert]
    · intro c C' hc'
      rw [hbs'] at hc'
      split at hc'
      · rename_i h; subst h; cases hc'; rw [hns', if_pos rfl]
      · rename_i hcb
        have hcC : X.t.bs !! c = some C' := hc'
        exact Hd bl B hb n (by simp [hr]) c C' hcC hcb
  have Hob' : T'.bobjs !! bl = some B' := bobjs_bkt T' bl B' (by rw [hbs', if_pos rfl])
  icases wtxHeap_reshape tx dq X [n] (fun _ => WObj.node bl rn) [bl] (fun _ => B)
    (nodup_one n) (by intro l hl; rw [List.mem_singleton.1 hl]; exact Hon)
    (nodup_one bl) (by intro l hl; rw [List.mem_singleton.1 hl]; exact Hob) $$ H
    with ⟨⟨Hn, -⟩, ⟨Hb, -⟩, Hf, Hrf, Hback⟩
  iapply Hback $$ %(X.kill bl B' n rn) %(fun _ => WObj.node bl rn) %(fun _ => B')
    [] [Hn] [Hb] [Hf] [Hrf]
  · ipureintro
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩
    · intro l hl; rw [List.mem_singleton.1 hl, hT']; exact Hon'
    · intro l hl; rw [List.mem_singleton.1 hl, hT']; exact Hob'
    · intro k hk
      refine ⟨by rw [hT']; exact hagree k hk, ?_⟩
      simp only [List.mem_singleton] at hk
      show k ∈ X.live.delete n ↔ k ∈ X.live
      simp only [GMap.mem_iff, GMap.lookup_delete_ne _ (Ne.symm hk)]
    · intro k hk
      exact ⟨by rw [hT']; exact hagreeB k hk, Iff.rfl⟩
    · refine heapOK_of tx X _ Hok rfl Hd' ?_ ?_ rfl ?_ rfl
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
        by_cases hkL : k ∈ [n]
        · rw [List.mem_singleton.1 hkL, Hon']; rfl
        · rw [hagree k hkL]; exact hk
  · iapply BigSepL.bigSepL_singleton.2
    iapply objOwn_weaken X.v n dq _ _ _ ?_ $$ Hn
    intro h
    simp only [decide_eq_true_eq] at h
    exact absurd h (by show ¬ (n ∈ X.live.delete n); simp [GMap.mem_iff])
  · iapply BigSepL.bigSepL_singleton.2
    have hbl' : decide (bl ∈ (X.kill bl B' n rn).liveB) = decide (bl ∈ X.liveB) := rfl
    rw [hbl', objOwn_bkt_eq _ _ _ _ B B' h1 h2 h3 h4 h5 h6 h7]
    iexact Hb
  · rw [txFields_congr tx dq (X.kill bl B' n rn) X rfl rfl rfl rfl]; iexact Hf
  · iexact Hrf

end heap

end bbolt
end EtcdGrove
end Perennial
