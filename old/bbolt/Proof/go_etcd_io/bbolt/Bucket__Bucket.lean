module
public import Spec.go_etcd_io.bbolt.Bucket__Bucket
public import Spec.go_etcd_io.bbolt.Bucket__Cursor
public import Spec.go_etcd_io.bbolt.Cursor__seek
public import Spec.go_etcd_io.bbolt.Bucket__openBucket
public import Proof.go_etcd_io.bbolt.BucketIter

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

theorem Bucket.Bucket.wp_proof (hCursor : Bucket.Cursor.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek.spec (GF := GF) (hG := hG))
    (hopen : Bucket.openBucket.spec (GF := GF) (hG := hG)) :
    Bucket.Bucket.spec (GF := GF) (hG := hG) := by
  intro bl V q name nb dn Hbm Hwr
  wp_start as ⟨HR, Hst, Hn⟩
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  icases (bktR_split' bl V q.half q.half q (Qp.half_add_half q).symm).1 $$ HR with ⟨HR1, HR2⟩
  icases bktR_acc _ _ _ $$ HR1 with ⟨%Hok, Hctx1, Hpgs1, HR1back⟩
  icases (bktCtx_explicit _ _ _).1 $$ Hctx1 with ⟨Hbk, Hib, Htxp, %Hcx⟩
  wp_auto
  rw [decide_eq_true Hbm]
  simp only [Bool.not_true]
  try wp_auto
  ihave Hctx1 := (bktCtx_explicit bl V q.half).2 $$ [Hbk Hib Htxp]
  · iframe; ipureintro; exact Hcx
  wp_apply hCursor bl V q.half $$ [Hctx1 Hpgs1 Hst] as %cl ⟨Hc, Hst⟩
  · iframe
  wp_apply hseek cl bl V q.half [] name nb dn Hok.1 (treeOK_wfAt V Hok.2) $$ [Hc Hn]
    as %es %r %pg ⟨%Hs, Hc, Hn⟩
  · iframe
  obtain ⟨Hlt, Hseek⟩ := Hs
  obtain ⟨pid, pre, Hes, -, Hwfp, Hpa, Hnd, Hlen, Hfl, Hlw, Hli, Hcar⟩ := leafTop_facts V es r pg Hok.1 Hlt
  icases curI_drop _ _ _ _ _ $$ Hc with ⟨Hctx1, Hpgs1⟩
  try wp_auto
  by_cases Hin : sint.Z r.index' < pageCount pg
  · have H0 : 0 ≤ sint.Z r.index' := Hseek.1
    rw [kv_inside r.page' pg _ H0 Hin]
    simp only
    obtain ⟨i, Hi⟩ : ∃ i : Nat, (i : Int) = sint.Z r.index' := ⟨_, Int.toNat_of_nonneg H0⟩
    have Hit : (sint.Z r.index').toNat = i := by omega
    rw [Hit]
    have Hic : i < pageCount pg := by omega
    icases bktPages_acc V q.half pid _ pg Hok.1 Hpa $$ Hpgs1 with ⟨Hpg, Hpgsback⟩
    icases leaf_key_acc _ _ pg i Hlw Hic Hcar $$ Hpg with ⟨Hks, Hkback⟩
    wp_apply bytes.wp_Equal name _ dn (DFrac.own q.half) nb (leafKey pg i) $$ [Hn Hks] as ⟨Hn, Hks⟩
    · iframe
    ihave Hpg := Hkback $$ Hks
    ihave Hpgs1 := Hpgsback $$ Hpg
    by_cases Heq : nb = leafKey pg i
    · rw [decide_eq_true Heq]
      simp only [Bool.not_true]
      try wp_auto
      by_cases Hf : W32 (leafFlags pg i) &&& W32 1 = W32 0
      · rw [decide_eq_true Hf]
        try wp_auto
        ihave HR1 := HR1back $$ Hctx1 Hpgs1
        ihave HR := (bktR_split' bl V q.half q.half q (Qp.half_add_half q).symm).2 $$ [HR1 HR2]
        · iframe
        iapply HΦ
        iframe
        ileft
        iframe
        ipureintro; rfl
      · rw [decide_eq_false Hf]
        try wp_auto
        have Hfb : leafFlags pg i % 2 = bucketLeafFlag :=
          flag_bit _ (by have := leAt_lt pg (elemOff i) 4; unfold leafFlags; omega) Hf
        have Hbwf := nestedWF V pid _ pg i Hok.2 Hwfp Hpa Hfl Hic Hfb
        obtain ⟨H16, Hinl⟩ := bucketWF_len _ _ _ Hbwf
        icases (bktCtx_explicit _ _ _).1 $$ Hctx1 with ⟨Hbk, Hib, Htxp, %Hcx⟩
        have Htx' : V.bkt.tx' = V.tx := Hcx.2.2.2.2.2
        unfold txPart
        icases Htxp with ⟨Ht, Hd, Hps⟩
        icases Tx_rest_stats_writable _ _ _ $$ Ht with ⟨Hw, Htback⟩
        rw [Hwr]
        icases bktPages_acc V q.half pid _ pg Hok.1 Hpa $$ Hpgs1 with ⟨Hpg, Hpgsback⟩
        icases leaf_value_acc _ _ pg i Hlw Hic Hcar $$ Hpg with ⟨Hvs, Hvback⟩
        have hop := hopen bl V.bkt (DFrac.own q.half) (DFrac.own q.half)
          (sliceAt r.page' (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i)) (leafValue pg i)
          (DFrac.own q.half) H16 Hinl
        rw [Htx'] at hop
        wp_apply hop $$ [Hbk Hw Hvs] as %cl %ibl ⟨Hbk, Hw, Hvs, Hcl, Hal⟩
        · iframe
        ihave Hpg := Hvback $$ Hvs
        ihave Hpgs1 := Hpgsback $$ Hpg
        ihave Ht := Htback $$ Hw
        ihave Hctx1 := (bktCtx_explicit bl V q.half).2 $$ [Hbk Hib Ht Hd Hps]
        · unfold txPart; iframe; ipureintro; exact Hcx
        ihave HR1 := HR1back $$ Hctx1 Hpgs1
        try wp_auto
        rw [decide_eq_true Hbm]
        simp only [Bool.not_true]
        try wp_auto
        have Hne : leafValue pg i ≠ [] := by intro h; rw [h] at H16; simp at H16
        obtain ⟨rq, Hrq⟩ := childQ_split q.half
        icases bktR_lend bl V q.half (childQ q.half) rq Hrq $$ HR2 with ⟨-, Hctx2, Hpgs2, Hview2, Hlend⟩
        icases (bktCtx_explicit _ _ _).1 $$ Hctx2 with ⟨Hbk2, Hib2, Htxp2, -⟩
        have Hnest : ∀ ibl', nestedOK V (childView V (leafValue pg i) ibl') nb :=
          fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, pid, _, pg, i, Hpa, Hfl, Hic, Heq.symm, Hfb, rfl⟩
        icases Hal with (%Hal | ⟨%c, %Hal, Hc, -⟩)
        · subst Hal
          have Hbound : elemOff i + leafPos pg i + leafKsize pg i + leafVsize pg i ≤ pg.length := by
            have := (Hlw.2.2.1 i Hic).1; have := Hlw.1; omega
          have HcarV : (r.page' +ₗ ((elemOff i + leafPos pg i + leafKsize pg i : Nat) : Int)).locCar ≠ 0 := by
            simpa [Loc.add] using Hcar
          icases bktPages_acc V _ pid _ pg Hok.1 Hpa $$ Hpgs2 with ⟨Hpg2, Hpgsback2⟩
          icases (bytesPointsto_around r.page' _ pg _ _ Hbound).1 $$ Hpg2 with ⟨Hpre, Hmid, Hpost⟩
          icases child_build cl _ V (leafValue pg i) (childQ q.half) (childQ_lt_one _) Hok.1 Hcx Hbwf
            HcarV $$ [Hcl Hmid Htxp2 Hview2] with ⟨HRc, Hcback⟩
          · iframe
          iapply HΦ
          iframe Hst Hn
          iright
          iexists _, childQ q.half
          iframe HR1 HRc
          isplitr
          · ipureintro; exact Hnest _
          iintro HRc
          icases Hcback $$ HRc with ⟨Hmid, Htxp2, Hview2⟩
          ihave Hpg2 := (bytesPointsto_around r.page' _ pg _ _ Hbound).2 $$ [Hpre Hmid Hpost]
          · unfold leafValue; iframe
          ihave Hpgs2 := Hpgsback2 $$ Hpg2
          ihave Hctx2 := (bktCtx_explicit bl V _).2 $$ [Hbk2 Hib2 Htxp2]
          · iframe; ipureintro; exact Hcx
          iapply Hlend $$ Hctx2 Hpgs2 Hview2
        · subst Hal
          icases slice_car_keep c _ _ Hne $$ Hc with ⟨%Hcc, Hc⟩
          icases (ownSlice_bytes c _ _ Hne).1 $$ Hc with ⟨Hcb, -⟩
          obtain ⟨rc, Hrc⟩ := Qp.lt_iff_exists_add.1 (childQ_lt_one q.half)
          icases (bytes_split' c.ptr _ _ rc 1 Hrc.symm).1 $$ Hcb with ⟨Hcb, -⟩
          icases child_build cl _ V (leafValue pg i) (childQ q.half) (childQ_lt_one _) Hok.1 Hcx Hbwf
            Hcc $$ [Hcl Hcb Htxp2 Hview2] with ⟨HRc, Hcback⟩
          · iframe
          iapply HΦ
          iframe Hst Hn
          iright
          iexists _, childQ q.half
          iframe HR1 HRc
          isplitr
          · ipureintro; exact Hnest _
          iintro HRc
          icases Hcback $$ HRc with ⟨-, Htxp2, Hview2⟩
          ihave Hctx2 := (bktCtx_explicit bl V _).2 $$ [Hbk2 Hib2 Htxp2]
          · iframe; ipureintro; exact Hcx
          iapply Hlend $$ Hctx2 Hpgs2 Hview2
    · rw [decide_eq_false Heq]
      simp only [Bool.not_false]
      try wp_auto
      ihave HR1 := HR1back $$ Hctx1 Hpgs1
      ihave HR := (bktR_split' bl V q.half q.half q (Qp.half_add_half q).symm).2 $$ [HR1 HR2]
      · iframe
      iapply HΦ
      iframe
      ileft
      iframe
      ipureintro; rfl
  · rw [kv_past r.page' pg _ (by omega)]
    simp only
    ihave Hnil : slice.nil ↦* ([] : List w8) $$ []
    · iapply ownSlice_nil
    wp_apply bytes.wp_Equal name _ dn (DFrac.own 1) nb [] $$ [Hn Hnil] as ⟨Hn, -⟩
    · iframe
    by_cases Heq : nb = []
    · rw [decide_eq_true Heq]
      simp only [Bool.not_true]
      try wp_auto
      ihave HR1 := HR1back $$ Hctx1 Hpgs1
      ihave HR := (bktR_split' bl V q.half q.half q (Qp.half_add_half q).symm).2 $$ [HR1 HR2]
      · iframe
      iapply HΦ
      iframe
      ileft
      iframe
      ipureintro; rfl
    · rw [decide_eq_false Heq]
      simp only [Bool.not_false]
      try wp_auto
      ihave HR1 := HR1back $$ Hctx1 Hpgs1
      ihave HR := (bktR_split' bl V q.half q.half q (Qp.half_add_half q).symm).2 $$ [HR1 HR2]
      · iframe
      iapply HΦ
      iframe
      ileft
      iframe
      ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
