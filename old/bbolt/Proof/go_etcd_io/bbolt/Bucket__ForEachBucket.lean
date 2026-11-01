module
public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket
public import Spec.go_etcd_io.bbolt.Bucket__Cursor
public import Spec.go_etcd_io.bbolt.Cursor__first
public import Spec.go_etcd_io.bbolt.Cursor__next

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

theorem Bucket.ForEachBucket.wp_proof (hCursor : Bucket.Cursor.spec (GF := GF) (hG := hG))
    (hfirst : Cursor.first.spec (GF := GF) (hG := hG))
    (hnext : Cursor.next.spec (GF := GF) (hG := hG)) :
    Bucket.ForEachBucket.spec (GF := GF) (hG := hG) := by
  intro bl V q fn I
  wp_start as ⟨HR, Hst, HI, #Hfn⟩
  isimp only [forEachBucketFn] at Hfn
  icases bktR_acc _ _ _ $$ HR with ⟨%Hok, Hctx, Hpgs, HRback⟩
  isimp only [bktCtx] at Hctx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, Hbk, Hib, Ht, Hdata, Hps, %Hcx⟩
  icases Tx_rest_stats_db _ _ _ $$ Ht with ⟨Htdb, Htback⟩
  wp_auto
  have Hdn : t.db' ≠ null := by rw [Hcx.2.2.2.1]; exact Hcx.2.2.2.2.2.2.1
  rw [decide_eq_false Hdn]
  try wp_auto
  ispecialize Htback $$ Htdb
  ihave Hctx : bktCtx bl V q $$ [Hbk Hib Htback Hdata Hps]
  · unfold bktCtx; iexists bv, ib, t, dbl; iframe; ipureintro; exact Hcx
  wp_apply hCursor bl V q $$ [Hctx Hpgs Hst] as %cl ⟨Hc, Hst⟩
  · iframe
  try wp_auto
  wp_apply hfirst cl bl V q [] Hok.1 (treeOK_wfAt V Hok.2) $$ [Hc] as %es %k %v %f ⟨%Hf, Hc⟩
  · iframe
  try wp_auto
  ihave IH : iprop(∃ (es1 : List elemRef) (k1 v1 : GoSlice) (f1 : w32),
      "k" ∷ k_ptr ↦ k1 ∗ "flags" ∷ flags_ptr ↦ f1 ∗ "Hc" ∷ curI cl bl V q es1 ∗
      "%Hkv" ∷ ⌜cursorOK V es1 ∧ kvOK V es1 k1 v1 f1⌝ ∗ "HI" ∷ I ∗ "Hst" ∷ txStats V.tx)
      $$ [k flags Hc HI Hst]
  · iexists es, k, v, f; iframe; ipureintro; exact ⟨Hf.1, Hf.2.2⟩
  wp_for IH
  by_cases Hkn : k1 = slice.nil
  · rw [decide_eq_true Hkn]
    have Hft : decide ((#false : val) = #true) = false := decide_eq_false (by
      intro h; have := intoVal_eq_iff.1 h; cases this)
    simp only [Bool.not_true]
    rw [Hft, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    simp only [_root_.decide_true, ↓reduceIte]
    try wp_auto
    icases curI_drop _ _ _ _ _ $$ Hc with ⟨Hctx, Hpgs⟩
    ihave HR := HRback $$ Hctx Hpgs
    iapply HΦ
    iframe
  · rw [decide_eq_false Hkn]
    simp only [Bool.not_false, _root_.decide_true, ↓reduceIte]
    try wp_auto
    obtain ⟨r, pg, Hlt, He, H0, Hin⟩ := kvOK_some V es1 k1 v1 f1 Hok.1 Hkv.2 Hkn
    have Hk1 : k1 = (kvResult r.page' pg (sint.Z r.index')).1 := congrArg Prod.fst He
    have Hf1 : f1 = (kvResult r.page' pg (sint.Z r.index')).2.2 := congrArg (·.2.2) He
    by_cases Hfl : f1 &&& W32 1 = W32 0
    · rw [decide_eq_true Hfl]
      simp only [Bool.not_true]
      try wp_auto
      wp_for_post
      wp_apply hnext cl bl V q es1 Hok.1 Hkv.1 $$ [Hc] as %es2 %k2 %v2 %f2 ⟨%Hn2, Hc⟩
      · iframe
      try wp_auto
      iframe
      iexists es2, k2, v2, f2
      iframe
      ipureintro; exact ⟨Hn2.1, Hn2.2.2⟩
    · rw [decide_eq_false Hfl]
      simp only [Bool.not_false]
      try wp_auto
      isimp only [curI] at Hc
      icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
      icases kv_elem_acc V q es1 r pg Hok.1 Hlt H0 Hin $$ Hpgs with ⟨%kb, %vb, %Hel, Hks, Hvs, Hback⟩
      rw [← Hf1] at Hel
      rw [← Hk1]
      wp_apply Hfn $$ %k1 %kb %(DFrac.own q.half) [HI Hst Hks]
        as %err ⟨HI, Hst, Hks⟩
      · iframe; ipureintro; exact ⟨f1, Hel.2, Hfl⟩
      ihave Hpgs := Hback $$ Hks Hvs
      ihave Hc : curI cl bl V q es1 $$ [Hcl Hs Hcap Hctx Hpgs]
      · unfold curI; iexists cv; iframe; ipureintro; exact Hb
      cases err with
      | nil =>
        try wp_auto
        wp_for_post
        wp_apply hnext cl bl V q es1 Hok.1 Hkv.1 $$ [Hc] as %es2 %k2 %v2 %f2 ⟨%Hn2, Hc⟩
        · iframe
        try wp_auto
        iframe
        iexists es2, k2, v2, f2
        iframe
        ipureintro; exact ⟨Hn2.1, Hn2.2.2⟩
      | ok e =>
        try wp_auto
        wp_for_post
        icases curI_drop _ _ _ _ _ $$ Hc with ⟨Hctx, Hpgs⟩
        ihave HR := HRback $$ Hctx Hpgs
        iapply HΦ
        iframe

end proof

end bbolt
end EtcdGrove
end Perennial
