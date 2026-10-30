module
public import Spec.go_etcd_io.bbolt.Cursor__Seek
public import Proof.go_etcd_io.bbolt.CursorLemmas
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.Cursor__seek
public import Spec.go_etcd_io.bbolt.Cursor__next
public import Spec.go_etcd_io.bbolt.elemRef__count

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
theorem Cursor.Seek.wp_proof
    (hAssert : _root_.Perennial.EtcdGrove.bbolt.Assert.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek.spec (GF := GF) (hG := hG))
    (hcount : elemRef.count.spec (GF := GF) (hG := hG))
    (hnext : Cursor.next.spec (GF := GF) (hG := hG)) :
    Cursor.Seek.spec (GF := GF) (hG := hG) := by
  intro cl bl V q es key kb dk Hok Hwf
  wp_start as ⟨Hc, Hk⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  unfold curI
  icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  unfold bktCtx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, Hbk, Hib, Ht, Hdata, Hps, %Hcx⟩
  icases Tx_rest_stats_db _ _ _ $$ Ht with ⟨Htdb, Htback⟩
  wp_auto
  rw [Hb]
  try wp_auto
  have Hdn : t.db' ≠ null := by rw [Hcx.2.2.2.1]; exact Hcx.2.2.2.2.2.2.1
  rw [decide_eq_false Hdn]
  try wp_auto
  wp_apply hAssert
  ispecialize Htback $$ Htdb
  ihave Hc : curI cl bl V q es $$ [Hcl Hs Hcap Hbk Hib Htback Hdata Hps Hpgs]
  · unfold curI bktCtx; iexists cv; iframe; ipureintro; exact ⟨Hb, Hcx⟩
  try wp_auto
  wp_apply hseek cl bl V q es key kb dk Hok Hwf $$ [Hc Hk] as %es3 %r3 %pg3 ⟨%Hs3, Hc, Hk⟩
  · iframe
  obtain ⟨Hlt, -⟩ := Hs3
  unfold curI
  icases Hc with ⟨%cv3, %Hb3, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  obtain ⟨pid3, pre3, Hes3, -, -, Hpa3, Hn3, Hlen3, Hfl3, Hlw3, Hli3, Hc3⟩ := leafTop_facts V es3 r3 pg3 Hok Hlt
  subst Hes3
  ihave %Hsl3 := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_append, List.length_singleton] at Hsl3
  obtain ⟨Hix3, Hb3'⟩ := top_index cv3.stack' pre3.length Hsl3
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true Hb3')]
  icases ownSlice_elem_acc (sint.Z (cv3.stack'.len - W64 1)) r3 _ _ (pre3 ++ [r3]) Hb3'.1
    (by rw [Hix3]; simp) $$ Hs with ⟨Hr, Hsback⟩
  try wp_auto
  icases bktPages_acc V q pid3 _ pg3 Hok Hpa3 $$ Hpgs with ⟨Hpg, Hpgsback⟩
  wp_apply hcount _ r3 (DFrac.own 1) (DFrac.own q) pg3 Hn3 Hc3 Hlen3 $$ [Hr Hpg] as ⟨Hr, Hpg⟩
  · iframe
  ihave Hs := Hsback $$ %r3 Hr
  rw [Hix3, set_len_append]
  ihave Hpgs := Hpgsback $$ Hpg
  try wp_auto
  wp_if_destruct
  · ihave Hc : curI cl bl V q (pre3 ++ [r3]) $$ [Hcl Hs Hcap Hctx Hpgs]
    · unfold curI; iexists cv3; iframe; ipureintro; exact Hb3
    try wp_auto
    wp_apply hnext cl bl V q (pre3 ++ [r3]) Hok (Or.inr ⟨r3, pg3, Hlt⟩) $$ [Hc]
      as %es5 %k5 %v5 %f5 ⟨%Hn5, Hc⟩
    · iframe
    obtain ⟨Hcur5, -, Hkv5⟩ := Hn5
    try wp_auto
    ispecialize HΦ $$ %es5 %k5 %v5 %f5
    by_cases Hkn : k5 = slice.nil
    · rw [decide_eq_true Hkn]
      try wp_auto
      rw [kvOK_nil_key V es5 k5 v5 f5 Hok Hkv5 Hkn, Hkn]
      rw [Hkn] at Hkv5
      iapply HΦ
      isplitl []
      · ipureintro; exact ⟨Hcur5, Hkv5⟩
      unfold curI bktCtx
      iframe
    · rw [decide_eq_false Hkn]
      try wp_auto
      by_cases Hf : f5 &&& W32 1 = W32 0
      · rw [decide_eq_true Hf]
        try wp_auto
        have Hv : kvVal v5 f5 = v5 := by unfold kvVal; rw [ite_eq_left_of_eq_true _ _ (eq_true Hf)]
        rw [Hv]
        iapply HΦ
        isplitl []
        · ipureintro; exact ⟨Hcur5, Hkv5⟩
        unfold curI bktCtx
        iframe
      · rw [decide_eq_false Hf]
        try wp_auto
        have Hv : kvVal v5 f5 = slice.nil := by unfold kvVal; rw [ite_eq_right_of_eq_false _ _ (eq_false Hf)]
        rw [Hv]
        iapply HΦ
        isplitl []
        · ipureintro; exact ⟨Hcur5, Hkv5⟩
        unfold curI bktCtx
        iframe
  · ihave Hc : curI cl bl V q (pre3 ++ [r3]) $$ [Hcl Hs Hcap Hctx Hpgs]
    · unfold curI; iexists cv3; iframe; ipureintro; exact Hb3
    have Hkv3 : kvOK V (pre3 ++ [r3]) (kvResult r3.page' pg3 (sint.Z r3.index')).1 (kvResult r3.page' pg3 (sint.Z r3.index')).2.1 (kvResult r3.page' pg3 (sint.Z r3.index')).2.2 := Or.inr ⟨r3, pg3, Hlt, rfl⟩
    try wp_auto
    ispecialize HΦ $$ %(pre3 ++ [r3]) %(kvResult r3.page' pg3 (sint.Z r3.index')).1 %(kvResult r3.page' pg3 (sint.Z r3.index')).2.1 %(kvResult r3.page' pg3 (sint.Z r3.index')).2.2
    by_cases Hkn : (kvResult r3.page' pg3 (sint.Z r3.index')).1 = slice.nil
    · rw [decide_eq_true Hkn]
      try wp_auto
      rw [kvOK_nil_key V (pre3 ++ [r3]) (kvResult r3.page' pg3 (sint.Z r3.index')).1 (kvResult r3.page' pg3 (sint.Z r3.index')).2.1 (kvResult r3.page' pg3 (sint.Z r3.index')).2.2 Hok Hkv3 Hkn, Hkn]
      rw [Hkn] at Hkv3
      iapply HΦ
      isplitl []
      · ipureintro; exact ⟨(Or.inr ⟨r3, pg3, Hlt⟩), Hkv3⟩
      unfold curI bktCtx
      iframe
    · rw [decide_eq_false Hkn]
      try wp_auto
      by_cases Hf : (kvResult r3.page' pg3 (sint.Z r3.index')).2.2 &&& W32 1 = W32 0
      · rw [decide_eq_true Hf]
        try wp_auto
        have Hv : kvVal (kvResult r3.page' pg3 (sint.Z r3.index')).2.1 (kvResult r3.page' pg3 (sint.Z r3.index')).2.2 = (kvResult r3.page' pg3 (sint.Z r3.index')).2.1 := by unfold kvVal; rw [ite_eq_left_of_eq_true _ _ (eq_true Hf)]
        rw [Hv]
        iapply HΦ
        isplitl []
        · ipureintro; exact ⟨(Or.inr ⟨r3, pg3, Hlt⟩), Hkv3⟩
        unfold curI bktCtx
        iframe
      · rw [decide_eq_false Hf]
        try wp_auto
        have Hv : kvVal (kvResult r3.page' pg3 (sint.Z r3.index')).2.1 (kvResult r3.page' pg3 (sint.Z r3.index')).2.2 = slice.nil := by unfold kvVal; rw [ite_eq_right_of_eq_false _ _ (eq_false Hf)]
        rw [Hv]
        iapply HΦ
        isplitl []
        · ipureintro; exact ⟨(Or.inr ⟨r3, pg3, Hlt⟩), Hkv3⟩
        unfold curI bktCtx
        iframe

end proof

end bbolt
end EtcdGrove
end Perennial
