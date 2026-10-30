module
public import Spec.go_etcd_io.bbolt.Cursor__Last
public import Proof.go_etcd_io.bbolt.CursorLemmas
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Spec.go_etcd_io.bbolt.elemRef__count
public import Spec.go_etcd_io.bbolt.Cursor__last
public import Spec.go_etcd_io.bbolt.Cursor__prev
public import Spec.go_etcd_io.bbolt.Cursor__keyValue

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxHeartbeats 400000 in
theorem Cursor.Last.wp_proof
    (hAssert : _root_.Perennial.EtcdGrove.bbolt.Assert.spec (GF := GF) (hG := hG))
    (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hpageNode : Bucket.pageNode.spec (GF := GF) (hG := hG))
    (hcount : elemRef.count.spec (GF := GF) (hG := hG))
    (hlast : Cursor.last.spec (GF := GF) (hG := hG))
    (hprev : Cursor.prev.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue.spec (GF := GF) (hG := hG)) :
    Cursor.Last.spec (GF := GF) (hG := hG) := by
  intro cl bl V q es Hok Hwf
  wp_start as Hc
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  unfold curI
  icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  unfold bktCtx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, Hbk, Hib, Ht, Hdata, Hps, %Hcx⟩
  ihave %Hwfs := ownSlice_wf _ _ _ $$ Hs
  icases Tx_rest_stats_db _ _ _ $$ Ht with ⟨Htdb, Ht⟩
  wp_auto
  rw [Hb]
  try wp_auto
  have Hdn : t.db' ≠ null := by rw [Hcx.2.2.2.1]; exact Hcx.2.2.2.2.2.2.1
  rw [decide_eq_false Hdn]
  try wp_auto
  wp_apply hAssert
  ispecialize Ht $$ Htdb
  try wp_auto
  have h00 : sint.Z (W64 0) = 0 := rfl
  have hn0 : sint.nat (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
  icases ownSlice_slice_with_cap (W64 0) (W64 0) cv.stack' _ ⟨by omega, by omega, by omega⟩ $$ [Hs Hcap]
    with ⟨-, Hs, Hcap⟩
  · iframe
  rw [hn0, show subslice 0 0 es = ([] : List elemRef) by simp [subslice]]
  try wp_auto
  wp_method_call
  try wp_auto
  rw [Hb]
  try wp_auto
  wp_apply hRoot $$ [Hib] as Hib
  · iframe
  rw [Hcx.1]
  ihave Hctx : bktCtx bl V q $$ [Hbk Hib Ht Hdata Hps]
  · unfold bktCtx; iframe; ipureintro; exact Hcx
  try wp_auto
  obtain ⟨p, pg, Hpa, Hlen, -, -, Hkind⟩ := wfAt_page V V.root Hok Hwf
  wp_apply pageNode_view hpageNode bl V q V.root p pg Hok Hwf Hpa $$ [Hctx Hpgs] as ⟨Hctx, Hpgs⟩
  · iframe
  try wp_auto
  have Hc0 := pageAt_car V V.root p pg Hok Hpa
  icases bktPages_acc V q V.root p pg Hok Hpa $$ Hpgs with ⟨Hpg, Hpgsback⟩
  wp_apply hcount _ { page' := p, node' := null, index' := W64 0 } (DFrac.own 1) (DFrac.own q) pg
    rfl Hc0 Hlen $$ [ref Hpg] as ⟨ref, Hpg⟩
  · iframe
  ispecialize Hpgsback $$ Hpg
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs, Hcap, -⟩
  try wp_auto
  have Hcnt : pageCount pg < 65536 := by have := leAt_lt pg 10 2; unfold pageCount; omega
  have Hcp : curPath V V.root ([] ++ [{ page' := p, node' := null, index' := W64 (pageCount pg) - W64 1 }])
      V.root { page' := p, node' := null, index' := W64 (pageCount pg) - W64 1 } pg := by
    refine ⟨[], rfl, rfl, Hwf, rfl, Hpa, ?_⟩
    rcases Hkind with ⟨Hl, -⟩ | ⟨Hbb, Hbw', -⟩
    · refine Or.inr ⟨Hl, ?_⟩
      unfold leafIdx
      by_cases h0 : pageCount pg = 0
      · simp only [h0]; constructor <;> word
      · constructor <;> word
    · have := Hbw'.1
      exact Or.inl ⟨Hbb, by word, by word⟩
  wp_apply hlast cl bl V q _ V.root _ pg Hok Hcp $$ [Hcl Hs Hcap Hctx Hpgsback] as %es3 %r3 %pg3 ⟨%Hlt, Hc⟩
  · unfold curI bktCtx
    iexists _
    iframe
    ipureintro; rfl
  ihave IH : iprop(∃ (es4 : List elemRef) (r4 : elemRef) (pg4 : List w8),
      "c" ∷ c_ptr ↦ cl ∗ "%Hl4" ∷ ⌜leafTop V es4 r4 pg4⌝ ∗ "Hc" ∷ curI cl bl V q es4) $$ [c Hc]
  · iexists es3, r3, pg3; iframe; ipureintro; exact Hlt
  wp_for IH
  unfold curI
  icases Hc with ⟨%cv4, %Hb4, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  obtain ⟨pid4, pre4, Hes4, -, -, Hpa4, Hn4, Hlen4, Hfl4, Hlw4, Hli4, Hc4⟩ := leafTop_facts V es4 r4 pg4 Hok Hl4
  subst Hes4
  ihave %Hsl4 := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_append, List.length_singleton] at Hsl4
  obtain ⟨Hix4, Hb4'⟩ := top_index cv4.stack' pre4.length Hsl4
  try wp_auto
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true Hb4')]
    icases ownSlice_elem_acc (sint.Z (cv4.stack'.len - W64 1)) r4 _ _ (pre4 ++ [r4]) Hb4'.1
      (by rw [Hix4]; simp) $$ Hs with ⟨Hr, Hsback⟩
    icases bktPages_acc V q pid4 _ pg4 Hok Hpa4 $$ Hpgs with ⟨Hpg, Hpgsback⟩
    wp_apply hcount _ r4 (DFrac.own 1) (DFrac.own q) pg4 Hn4 Hc4 Hlen4 $$ [Hr Hpg] as ⟨Hr, Hpg⟩
    · iframe
    ihave Hs := Hsback $$ %r4 Hr
    rw [Hix4, set_len_append]
    ihave Hpgs := Hpgsback $$ Hpg
    have Hcnt4 : pageCount pg4 < 65536 := by have := leAt_lt pg4 10 2; unfold pageCount; omega
    try wp_auto
    by_cases Hc0 : pageCount pg4 = 0
    · rw [decide_eq_true (by rw [Hc0]; rfl)]
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      try wp_auto
      ihave Hc : curI cl bl V q (pre4 ++ [r4]) $$ [Hcl Hs Hcap Hctx Hpgs]
      · unfold curI; iexists cv4; iframe; ipureintro; exact Hb4
      wp_apply hprev cl bl V q _ Hok Hwf (Or.inr ⟨r4, pg4, Hl4⟩) $$ [Hc] as %es5 %k5 %v5 %f5 ⟨%Hp5, Hc⟩
      · iframe
      obtain ⟨Hcur5, Hne5, -⟩ := Hp5
      obtain ⟨r5, pg5, Hl5⟩ := Hcur5.resolve_left (Hne5 (by simp))
      try wp_auto
      wp_for_post
      iframe
      iexists es5, r5, pg5
      unfold curI
      iframe
      ipureintro; exact Hl5
    · rw [decide_eq_false (w64_nat_ne_zero _ (by omega) Hc0)]
      have Hft : decide ((#false : val) = #true) = false := decide_eq_false (by
        intro h; have := intoVal_eq_iff.1 h; cases this)
      rw [Hft, ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
        ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true rfl))]
      try wp_auto
      have Hl0 : cv4.stack'.len ≠ W64 0 := fun h => by
        rw [h] at Hb4'; have : sint.Z (W64 0) = 0 := rfl; omega
      rw [decide_eq_false Hl0]
      try wp_auto
      icases bktPages_acc V q pid4 _ pg4 Hok Hpa4 $$ Hpgs with ⟨Hpg, Hpgsback⟩
      wp_apply hkv cl cv4 (DFrac.own 1) (pre4 ++ [r4]) (DFrac.own 1) r4 (DFrac.own q) pg4 (by simp)
        Hn4 Hc4 Hlen4 Hfl4 Hlw4 (Hli4.2.imp_right (·.2)) $$ [Hcl Hs Hpg] as ⟨Hcl, Hs, Hpg⟩
      · iframe
      ispecialize Hpgsback $$ Hpg
      try wp_auto
      ispecialize HΦ $$ %(pre4 ++ [r4]) %(kvResult r4.page' pg4 (sint.Z r4.index')).1
        %(kvResult r4.page' pg4 (sint.Z r4.index')).2.1 %(kvResult r4.page' pg4 (sint.Z r4.index')).2.2
      by_cases Hf : (kvResult r4.page' pg4 (sint.Z r4.index')).2.2 &&& W32 1 = W32 0
      · rw [decide_eq_true Hf]
        try wp_auto
        have Hv : kvVal (kvResult r4.page' pg4 (sint.Z r4.index')).2.1
            (kvResult r4.page' pg4 (sint.Z r4.index')).2.2 = (kvResult r4.page' pg4 (sint.Z r4.index')).2.1 := by
          unfold kvVal; rw [ite_eq_left_of_eq_true _ _ (eq_true Hf)]
        rw [Hv]
        iapply HΦ
        isplitl []
        · ipureintro; exact ⟨Or.inr ⟨r4, pg4, Hl4⟩, Or.inr ⟨r4, pg4, Hl4, rfl⟩⟩
        iexists cv4
        unfold bktCtx
        iframe
        ipureintro; exact Hb4
      · rw [decide_eq_false Hf]
        try wp_auto
        have Hv : kvVal (kvResult r4.page' pg4 (sint.Z r4.index')).2.1
            (kvResult r4.page' pg4 (sint.Z r4.index')).2.2 = slice.nil := by
          unfold kvVal; rw [ite_eq_right_of_eq_false _ _ (eq_false Hf)]
        rw [Hv]
        iapply HΦ
        isplitl []
        · ipureintro; exact ⟨Or.inr ⟨r4, pg4, Hl4⟩, Or.inr ⟨r4, pg4, Hl4, rfl⟩⟩
        iexists cv4
        unfold bktCtx
        iframe
        ipureintro; exact Hb4
  · try wp_auto
    have Hl0 : cv4.stack'.len ≠ W64 0 := fun h => by
      rw [h] at Hb4'; have : sint.Z (W64 0) = 0 := rfl; omega
    rw [decide_eq_false Hl0]
    try wp_auto
    icases bktPages_acc V q pid4 _ pg4 Hok Hpa4 $$ Hpgs with ⟨Hpg, Hpgsback⟩
    wp_apply hkv cl cv4 (DFrac.own 1) (pre4 ++ [r4]) (DFrac.own 1) r4 (DFrac.own q) pg4 (by simp)
      Hn4 Hc4 Hlen4 Hfl4 Hlw4 (Hli4.2.imp_right (·.2)) $$ [Hcl Hs Hpg] as ⟨Hcl, Hs, Hpg⟩
    · iframe
    ispecialize Hpgsback $$ Hpg
    try wp_auto
    ispecialize HΦ $$ %(pre4 ++ [r4]) %(kvResult r4.page' pg4 (sint.Z r4.index')).1
      %(kvResult r4.page' pg4 (sint.Z r4.index')).2.1 %(kvResult r4.page' pg4 (sint.Z r4.index')).2.2
    by_cases Hf : (kvResult r4.page' pg4 (sint.Z r4.index')).2.2 &&& W32 1 = W32 0
    · rw [decide_eq_true Hf]
      try wp_auto
      have Hv : kvVal (kvResult r4.page' pg4 (sint.Z r4.index')).2.1
          (kvResult r4.page' pg4 (sint.Z r4.index')).2.2 = (kvResult r4.page' pg4 (sint.Z r4.index')).2.1 := by
        unfold kvVal; rw [ite_eq_left_of_eq_true _ _ (eq_true Hf)]
      rw [Hv]
      iapply HΦ
      isplitl []
      · ipureintro; exact ⟨Or.inr ⟨r4, pg4, Hl4⟩, Or.inr ⟨r4, pg4, Hl4, rfl⟩⟩
      iexists cv4
      unfold bktCtx
      iframe
      ipureintro; exact Hb4
    · rw [decide_eq_false Hf]
      try wp_auto
      have Hv : kvVal (kvResult r4.page' pg4 (sint.Z r4.index')).2.1
          (kvResult r4.page' pg4 (sint.Z r4.index')).2.2 = slice.nil := by
        unfold kvVal; rw [ite_eq_right_of_eq_false _ _ (eq_false Hf)]
      rw [Hv]
      iapply HΦ
      isplitl []
      · ipureintro; exact ⟨Or.inr ⟨r4, pg4, Hl4⟩, Or.inr ⟨r4, pg4, Hl4, rfl⟩⟩
      iexists cv4
      unfold bktCtx
      iframe
      ipureintro; exact Hb4

end proof

end bbolt
end EtcdGrove
end Perennial
