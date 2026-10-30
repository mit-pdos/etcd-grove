module
public import Spec.go_etcd_io.bbolt.Cursor__first
public import Proof.go_etcd_io.bbolt.CursorLemmas
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Spec.go_etcd_io.bbolt.elemRef__count
public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack
public import Spec.go_etcd_io.bbolt.Cursor__next
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
theorem Cursor.first.wp_proof
    (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hpageNode : Bucket.pageNode.spec (GF := GF) (hG := hG))
    (hcount : elemRef.count.spec (GF := GF) (hG := hG))
    (hgoto : Cursor.goToFirstElementOnTheStack.spec (GF := GF) (hG := hG))
    (hnext : Cursor.next.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue.spec (GF := GF) (hG := hG)) :
    Cursor.first.spec (GF := GF) (hG := hG) := by
  intro cl bl V q es Hok Hwf
  wp_start as Hc
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  unfold curI
  icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  ihave %Hwfs := ownSlice_wf _ _ _ $$ Hs
  wp_auto
  have h00 : sint.Z (W64 0) = 0 := rfl
  have hn0 : sint.nat (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
  icases ownSlice_slice_with_cap (W64 0) (W64 0) cv.stack' _ ⟨by omega, by omega, by omega⟩ $$ [Hs Hcap]
    with ⟨-, Hs, Hcap⟩
  · iframe
  rw [hn0, show subslice 0 0 es = ([] : List elemRef) by simp [subslice]]
  try wp_auto
  -- `c.bucket.RootPage()`
  rw [Hb]
  unfold bktCtx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, Hbk, Hib, Ht, Hdata, Hps, %Hcx⟩
  wp_method_call
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
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs, Hcap, -⟩
  try wp_auto
  have Hcp : curPath V V.root ([] ++ [{ page' := p, node' := null, index' := W64 0 }]) V.root
      { page' := p, node' := null, index' := W64 0 } pg := by
    refine ⟨[], rfl, rfl, Hwf, rfl, Hpa, ?_⟩
    rcases Hkind with ⟨Hl, -⟩ | ⟨Hbb, Hbw', -⟩
    · exact Or.inr ⟨Hl, by simp only [h00]; omega, Or.inl (by simp only [h00]; omega)⟩
    · exact Or.inl ⟨Hbb, by simp only [h00]; omega, by have := Hbw'.1; simp only [h00]; omega⟩
  wp_apply hgoto cl bl V q _ V.root _ pg Hok Hcp $$ [Hcl Hs Hcap Hctx Hpgs] as %es3 %r3 %pg3 ⟨%Hlt, Hc⟩
  · unfold curI
    iexists _
    iframe
    ipureintro; rfl
  unfold curI
  icases Hc with ⟨%cv3, %Hb3, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  obtain ⟨pid3, pre3, Hes3, -, -, Hpa3, Hn3, Hlen3, Hfl3, -, -, Hc3⟩ := leafTop_facts V es3 r3 pg3 Hok Hlt
  subst Hes3
  ihave %Hsl3 := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_append, List.length_singleton] at Hsl3
  obtain ⟨Hix3, Hb3'⟩ := top_index cv3.stack' pre3.length Hsl3
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true Hb3')]
  icases ownSlice_elem_acc (sint.Z (cv3.stack'.len - W64 1)) r3 _ _ (pre3 ++ [r3]) Hb3'.1
    (by rw [Hix3]; simp) $$ Hs with ⟨Hr, Hsback⟩
  icases bktPages_acc V q pid3 _ pg3 Hok Hpa3 $$ Hpgs with ⟨Hpg, Hpgsback⟩
  wp_apply hcount _ r3 (DFrac.own 1) (DFrac.own q) pg3 Hn3 Hc3 Hlen3 $$ [Hr Hpg] as ⟨Hr, Hpg⟩
  · iframe
  ihave Hs := Hsback $$ %r3 Hr
  rw [Hix3, set_len_append]
  ispecialize Hpgsback $$ Hpg
  try wp_auto
  ihave Hc : curI cl bl V q (pre3 ++ [r3]) $$ [Hcl Hs Hcap Hctx Hpgsback]
  · unfold curI; iexists cv3; iframe; ipureintro; exact Hb3
  have Hcnt3 : pageCount pg3 < 65536 := by have := leAt_lt pg3 10 2; unfold pageCount; omega
  by_cases Hc0 : pageCount pg3 = 0
  · rw [decide_eq_true (by rw [Hc0]; rfl)]
    try wp_auto
    wp_apply hnext cl bl V q (pre3 ++ [r3]) Hok (Or.inr ⟨r3, pg3, Hlt⟩) $$ [Hc]
      as %es4 %k4 %v4 %f4 ⟨%Hn4, Hc⟩
    · iframe
    try wp_auto
    obtain ⟨Hcur4, Hne4, -⟩ := Hn4
    obtain ⟨r4, pg4, Hlt4⟩ := Hcur4.resolve_left (Hne4 (by simp))
    unfold curI
    icases Hc with ⟨%cvT, %HbT, Hcl, Hs, Hcap, Hctx, Hpgs⟩
    obtain ⟨pidT, preT, HesT, -, -, HpaT, HnT, HlenT, HflT, HlwT, HliT, HcT⟩ :=
      leafTop_facts V es4 r4 pg4 Hok Hlt4
    icases bktPages_acc V q pidT _ pg4 Hok HpaT $$ Hpgs with ⟨Hpg, Hpgsback⟩
    try wp_auto
    wp_apply hkv cl cvT (DFrac.own 1) es4 (DFrac.own 1) r4 (DFrac.own q) pg4 (by rw [HesT]; simp)
      HnT HcT HlenT HflT HlwT (HliT.2.imp_right (·.2)) $$ [Hcl Hs Hpg] as ⟨Hcl, Hs, Hpg⟩
    · iframe
    ispecialize Hpgsback $$ Hpg
    try wp_auto
    by_cases Hf : (kvResult r4.page' pg4 (sint.Z r4.index')).2.2 &&& W32 1 = W32 0
    · rw [decide_eq_true Hf]
      try wp_auto
      ispecialize HΦ $$ %es4 %(kvResult r4.page' pg4 (sint.Z r4.index')).1
        %(kvResult r4.page' pg4 (sint.Z r4.index')).2.1 %(kvResult r4.page' pg4 (sint.Z r4.index')).2.2
      unfold kvVal
      rw [ite_eq_left_of_eq_true _ _ (eq_true Hf)]
      iapply HΦ
      isplitl []
      · ipureintro; exact ⟨Or.inr ⟨r4, pg4, Hlt4⟩, by rw [HesT]; simp, Or.inr ⟨r4, pg4, Hlt4, rfl⟩⟩
      iexists cvT
      unfold bktCtx
      iframe
      ipureintro; exact HbT
    · rw [decide_eq_false Hf]
      try wp_auto
      ispecialize HΦ $$ %es4 %(kvResult r4.page' pg4 (sint.Z r4.index')).1
        %(kvResult r4.page' pg4 (sint.Z r4.index')).2.1 %(kvResult r4.page' pg4 (sint.Z r4.index')).2.2
      unfold kvVal
      rw [ite_eq_right_of_eq_false _ _ (eq_false Hf)]
      iapply HΦ
      isplitl []
      · ipureintro; exact ⟨Or.inr ⟨r4, pg4, Hlt4⟩, by rw [HesT]; simp, Or.inr ⟨r4, pg4, Hlt4, rfl⟩⟩
      iexists cvT
      unfold bktCtx
      iframe
      ipureintro; exact HbT
  · rw [decide_eq_false (w64_nat_ne_zero _ (by omega) Hc0)]
    try wp_auto
    unfold curI
    icases Hc with ⟨%cvT, %HbT, Hcl, Hs, Hcap, Hctx, Hpgs⟩
    obtain ⟨pidT, preT, HesT, -, -, HpaT, HnT, HlenT, HflT, HlwT, HliT, HcT⟩ :=
      leafTop_facts V (pre3 ++ [r3]) r3 pg3 Hok Hlt
    icases bktPages_acc V q pidT _ pg3 Hok HpaT $$ Hpgs with ⟨Hpg, Hpgsback⟩
    try wp_auto
    wp_apply hkv cl cvT (DFrac.own 1) (pre3 ++ [r3]) (DFrac.own 1) r3 (DFrac.own q) pg3 (by rw [HesT]; simp)
      HnT HcT HlenT HflT HlwT (HliT.2.imp_right (·.2)) $$ [Hcl Hs Hpg] as ⟨Hcl, Hs, Hpg⟩
    · iframe
    ispecialize Hpgsback $$ Hpg
    try wp_auto
    by_cases Hf : (kvResult r3.page' pg3 (sint.Z r3.index')).2.2 &&& W32 1 = W32 0
    · rw [decide_eq_true Hf]
      try wp_auto
      ispecialize HΦ $$ %(pre3 ++ [r3]) %(kvResult r3.page' pg3 (sint.Z r3.index')).1
        %(kvResult r3.page' pg3 (sint.Z r3.index')).2.1 %(kvResult r3.page' pg3 (sint.Z r3.index')).2.2
      unfold kvVal
      rw [ite_eq_left_of_eq_true _ _ (eq_true Hf)]
      iapply HΦ
      isplitl []
      · ipureintro; exact ⟨Or.inr ⟨r3, pg3, Hlt⟩, by rw [HesT]; simp, Or.inr ⟨r3, pg3, Hlt, rfl⟩⟩
      iexists cvT
      unfold bktCtx
      iframe
      ipureintro; exact HbT
    · rw [decide_eq_false Hf]
      try wp_auto
      ispecialize HΦ $$ %(pre3 ++ [r3]) %(kvResult r3.page' pg3 (sint.Z r3.index')).1
        %(kvResult r3.page' pg3 (sint.Z r3.index')).2.1 %(kvResult r3.page' pg3 (sint.Z r3.index')).2.2
      unfold kvVal
      rw [ite_eq_right_of_eq_false _ _ (eq_false Hf)]
      iapply HΦ
      isplitl []
      · ipureintro; exact ⟨Or.inr ⟨r3, pg3, Hlt⟩, by rw [HesT]; simp, Or.inr ⟨r3, pg3, Hlt, rfl⟩⟩
      iexists cvT
      unfold bktCtx
      iframe
      ipureintro; exact HbT

end proof

end bbolt
end EtcdGrove
end Perennial
