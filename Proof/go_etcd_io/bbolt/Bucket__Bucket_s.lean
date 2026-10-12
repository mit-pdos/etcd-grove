module
public import Spec.go_etcd_io.bbolt.Bucket__Bucket_s
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_w
public import Spec.go_etcd_io.bbolt.Cursor__seek_s
public import Proof.go_etcd_io.bbolt.ShapeOpen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt ShapeOpen

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Bucket.wp_sproof (hCur : Bucket.Cursor.wspec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek.sspec (GF := GF) (hG := hG))
    (hOpen : Bucket.openBucket.wspec (GF := GF) (hG := hG)) :
    Bucket.Bucket.sspec (GF := GF) (hG := hG) := by
  intro γ W txl T bl name nb dk Hbl
  obtain ⟨B, HB⟩ := Option.isSome_iff_exists.1 Hbl
  wp_start as ⟨Hown, Hsh, Hk⟩
  icases ownWriteTx_nonnull W txl T $$ Hown with ⟨%Hnn, Hown⟩
  icases txShape_facts γ W T $$ Hsh with ⟨%Hsf, Hsh⟩
  icases ownWriteTx_bkt_add2 W txl T bl B HB $$ Hown with ⟨%Hok, Hrest, Hmv, Hpm, Hb, Hv, Hclose⟩
  obtain ⟨HvOK, Hwr, Hdb, Hdbn, Hpm0, H2, Hhwm, Hroot, Hbs⟩ := Hok
  obtain ⟨Htx, Hclean, Hbmv⟩ := Hbs bl B HB
  ihave #Hby : (isPkgInit (PROP := IProp GF) pkg_id.bytes) $$ []
  · iPkgInit
  ihave %Hkl := ownSlice_len _ _ _ $$ Hk
  isimp only [TxW_rest_root] at Hrest
  icases Hrest with ⟨Hwritable, Hmanaged, Hdbf, Hmetaf, Hpages, Hstats, Hch, Hwf, %Htxn⟩
  rw [Hdb]
  isimp only [bktOwn] at Hb
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  ihave %Hbmnn := ownMap_not_nil _ _ _ $$ Hbm
  try wp_auto
  rw [decide_eq_false Hbmnn, Bool.not_false]
  try wp_auto
  wp_apply wp_bytes_to_string name nb dk $$ [Hk] as Hk
  · iframe
  try wp_auto
  wp_apply wp_map_lookup1 $$ [Hbm] as Hbm
  · iframe
  try wp_auto
  by_cases Hc0 : (B.bm !! nb).getD (zero_val Loc) = null
  · rw [Hc0, decide_eq_true rfl, Bool.not_true]
    try wp_auto
    try rw [Htx]
    wp_apply hCur bl B.bv (DFrac.own 1) T.t.stats' $$ [Hbv Hstats] as %cl %s ⟨Hcl, Hs, Hcap, Hbv, Hstats⟩
    · rw [Htx]; iframe
    try wp_auto
    have HwOK : wctxOK W (uint.nat T.mv.pgid') bl B txl T.pm :=
      ⟨HvOK, Hclean, Htx, fun id _ => by rw [Hpm0]; rfl⟩
    wp_apply hSeek cl { bucket' := bl, stack' := s } [] W (uint.nat T.mv.pgid') bl B txl T.t.pages' T.pm
      (DFrac.own 1) name nb dk rfl HwOK
      $$ [Hcl Hs Hcap Hbv Hib Hnm Hbm Hpo Hns Hv Hpages Hpm Hdbf Hk]
      as %cv' %path %k %v %f ⟨%Hsk, Hcl, Hs, Hcap, Hctx, Hk⟩
    · isplitl [Hcl]
      · iframe
      iframe
      unfold wctx
      isplitl [Hbv Hib Hnm Hbm Hpo Hns]
      · unfold bktOwn; iframe
      iframe
    try wp_auto
    obtain ⟨-, Hpath, -, -, Hsat, -⟩ := Hsk
    obtain ⟨bs, vb, Hres0⟩ := seek_res0 W _ bl B Hclean HvOK path (k, v, f) Hpath Hsat
    icases seekRes_key_acc W (uint.nat T.mv.pgid') bl B txl T.t.pages' T.pm (DFrac.own 1) k v f bs vb
      HvOK.1 Hclean Hres0 $$ Hctx with ⟨%dq, %Hres, Hkk, Hkback⟩
    wp_apply bytes.wp_Equal name k dk dq nb bs $$ [Hk Hkk] as ⟨Hk, Hkk⟩
    · iframe
    ihave Hctx := Hkback $$ Hkk
    try wp_auto
    try rw [Htx]
    by_cases Heq : nb = bs
    · rw [decide_eq_true Heq, Bool.not_true]
      try wp_auto
      by_cases Hf : f &&& W32 1 = W32 0
      · rw [decide_eq_true Hf]
        try wp_auto
        isimp only [wctx] at Hctx
        icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
        icases Hclose with ⟨Hclose, -⟩
        ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
        · ipureintro; exact ⟨Hclean, Htx, rfl⟩
        · unfold TxW_rest_root; simp only; rw [Hdb]; iframe; ipureintro; exact Htxn
        ihave Hsh := txShape_same γ W T (wtxUpd T _ bl B) bl B HB rfl $$ Hsh
        ispecialize HΦ $$ %(null) %_
        iapply HΦ
        iframe
        ipureintro; exact ⟨wtxSub_of_same _ _ (wtxSame_upd T _ bl B _ HB), Or.inl rfl⟩
      · rw [decide_eq_false Hf]
        try wp_auto
        obtain ⟨Hvb, Hent, Htk, src, Hsrc, Hacc⟩ :=
          seekRes_bkt W _ bl B Hclean HvOK (Hsf bl B HB).1 k v f bs vb Hres Hf
        subst Heq
        have Hnb : ¬ opened B nb := by
          intro h; unfold opened at h
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
          rw [hc] at Hc0; simp only [Option.getD_some] at Hc0
          obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 (Hbmv nb c hc)
          exact Hnn c C hC Hc0
        have H16 : 16 ≤ vb.length := by
          rcases Hvb.1 with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> exact h
        have Hinl16 : inBucketRoot vb = 0 → 16 < vb.length := by
          intro h0
          have := (Hvb.2 h0).2.2.2.1
          unfold inlinePage at this; simp at this; omega
        have Hvne : vb ≠ [] := by intro h; rw [h] at H16; simp at H16
        isimp only [wctx] at Hctx
        icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
        isimp only [bktOwn] at Hbk
        icases Hbk with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
        isimp only [wView] at Hv
        icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
        icases bktVal_acc W HvOK.1 bl B v vb src Hsrc Hacc $$ [Hpv Hns] with ⟨%dq, #Hsv, Hval, Hvback⟩
        · iframe
        icases slice_car_keep v vb dq Hvne $$ Hval with ⟨%Hvcar, Hval⟩
        wp_apply hOpen bl B.bv (DFrac.own 1) (DFrac.own 1) v vb dq H16 Hinl16 $$ [Hbv Hwritable Hval]
          as %cl %ibl %pgl %bm %nm ⟨Hbv, Hwritable, Hval, Hcl, Hibl, Hbm2, Hnm2, Hpg⟩
        · rw [Htx, Hwr]; iframe
        ihave Hv2 := Hvback $$ Hval
        icases Hv2 with ⟨Hpv, Hns⟩
        try wp_auto
        -- the opened bucket's inline page
        obtain ⟨csrc, Hcsrc⟩ : ∃ csrc : Src, csrc = Src.view ∨ csrc = Src.own DFrac.discard :=
          ⟨Src.view, Or.inl rfl⟩
        icases Hpg with (%Hpgl | Hpgb)
        · -- in place
          rw [decide_eq_false Hbmnn, Bool.not_false]
          try wp_auto
          wp_apply wp_bytes_to_string name nb dk $$ [Hk] as Hk
          · iframe
          try wp_auto
          wp_apply wp_mapInsert $$ [Hbm] as Hbm
          · iframe
          try wp_auto
          have Hpnn : inBucketRoot vb = 0 → pgl ≠ null := by
            intro _ h; rw [Hpgl] at h
            have : (v.ptr +ₗ 16).locCar = v.ptr.locCar := by simp [Loc.add]
            rw [h] at this; exact Hvcar this.symm
          ihave Hpo2 : inlPageOwn (GF := GF) W pgl vb src $$ []
          · unfold inlPageOwn
            by_cases hr : inBucketRoot vb = 0
            · rw [if_pos hr]
              rcases Hsrc with rfl | rfl
              · isimp only [srcOwn] at Hsv
                icases Hsv with %Hin
                ipureintro
                have := inViewLoc_sub W v.ptr vb 16 (vb.length - 16) Hin.1 (by omega)
                rw [bytesAt_drop] at this
                rw [Hpgl]; exact this
              · isimp only [srcOwn] at Hsv
                simp only
                rw [Hpgl]
                ihave Hb := slice_drop_bytes v DFrac.discard vb 16 H16 Hvne $$ Hsv
                unfold inlinePage
                iexact Hb
            · rw [if_neg hr]; ipureintro; trivial
          ihave Hcbk := childRec_own W cl txl ibl pgl bm nm vb src $$ [Hcl Hibl Hbm2 Hnm2 Hpo2]
          · rw [Htx]; iframe
          try rw [Htx]
          ihave Hbk : bktOwn (GF := GF) W bl ({ B with bm := <[nb := cl]> B.bm }) $$ [Hbv Hib Hnm Hbm Hpo Hns]
          · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W ({ B with bm := <[nb := cl]> B.bm }) B rfl rfl rfl); iexact Hpo
          ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
          · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
          have Hbm3 : ∀ n c, ({ B with bm := <[nb := cl]> B.bm }).bm !! n = some c → c = cl ∨ (T.bs !! c).isSome := by
            intro n c h
            by_cases e : n = nb
            · subst e; simp only at h; rw [GMap.lookup_insert] at h; exact Or.inl (Option.some.inj h).symm
            · simp only at h; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr (Hbmv _ c h)
          icases Hclose with ⟨-, Hclose⟩
          ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %({ B with bm := <[nb := cl]> B.bm }) %cl %(childRec txl ibl pgl bm nm vb src) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hcbk Hv
          · ipureintro; exact ⟨Hclean, Htx, Hbm3, bktClean_child W _ cl txl ibl pgl bm nm vb _ Hvb Hpnn Hsrc, rfl, rfl⟩
          · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
          icases Hown with ⟨Hown, %Hfr⟩
          have Hadd := txShape_add (GF := GF) γ W T { T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 } bl B nb cl (childRec txl ibl pgl bm nm vb src) vb HB Hfr Hent H16 rfl rfl rfl Htk
            ((bktToks_open γ W _ bl B cl nb vb Hclean HvOK Hnb Hent).trans
              (sep_mono .rfl (bktToks_child γ W txl ibl pgl bm nm vb src)))
          unfold bOpen at Hadd
          ihave Hsh := Hadd $$ Hsh
          ispecialize HΦ $$ %cl %_
          iapply HΦ
          iframe
          ipureintro; refine ⟨wtxSub_add T _ bl B _ cl _ HB, Or.inr ?_⟩
          show ((<[cl := _]> (<[bl := _]> T.bs)) !! cl).isSome; rw [GMap.lookup_insert]; rfl
        · -- in a copy
          ihave Hpgb := ((bytesPointsto_dfractional (GF := GF) pgl (vb.drop 16)).dfractional_persist
            (DFrac.own 1)) $$ Hpgb
          imod Hpgb
          haveI := (bytesPointsto_dfractional (GF := GF) pgl (vb.drop 16)).dfractional_persistent
          icases Hpgb with #Hpgb
          rw [decide_eq_false Hbmnn, Bool.not_false]
          try wp_auto
          wp_apply wp_bytes_to_string name nb dk $$ [Hk] as Hk
          · iframe
          try wp_auto
          wp_apply wp_mapInsert $$ [Hbm] as Hbm
          · iframe
          try wp_auto
          ihave %Hpc : ⌜inBucketRoot vb = 0 → pgl.locCar ≠ 0⌝ $$ []
          · by_cases hr0 : inBucketRoot vb = 0
            · have hne : vb.drop 16 ≠ [] := by
                intro h; have := Hinl16 hr0; have := congrArg List.length h; simp at this; omega
              ihave %h := bytesPointsto_car pgl DFrac.discard (vb.drop 16) hne $$ Hpgb
              ipureintro; exact fun _ => h
            · ipureintro; exact fun h => absurd h hr0
          have Hpnn : inBucketRoot vb = 0 → pgl ≠ null := fun h e => Hpc h (by rw [e]; rfl)
          ihave Hpo2 : inlPageOwn (GF := GF) W pgl vb (Src.own DFrac.discard) $$ []
          · unfold inlPageOwn
            by_cases hr : inBucketRoot vb = 0
            · rw [if_pos hr]; simp only; unfold inlinePage; iexact Hpgb
            · rw [if_neg hr]; ipureintro; trivial
          ihave Hcbk := childRec_own W cl txl ibl pgl bm nm vb (Src.own DFrac.discard) $$ [Hcl Hibl Hbm2 Hnm2 Hpo2]
          · rw [Htx]; iframe
          try rw [Htx]
          ihave Hbk : bktOwn (GF := GF) W bl ({ B with bm := <[nb := cl]> B.bm }) $$ [Hbv Hib Hnm Hbm Hpo Hns]
          · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W ({ B with bm := <[nb := cl]> B.bm }) B rfl rfl rfl); iexact Hpo
          ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
          · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
          have Hbm3 : ∀ n c, ({ B with bm := <[nb := cl]> B.bm }).bm !! n = some c → c = cl ∨ (T.bs !! c).isSome := by
            intro n c h
            by_cases e : n = nb
            · subst e; simp only at h; rw [GMap.lookup_insert] at h; exact Or.inl (Option.some.inj h).symm
            · simp only at h; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr (Hbmv _ c h)
          icases Hclose with ⟨-, Hclose⟩
          ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %({ B with bm := <[nb := cl]> B.bm }) %cl %(childRec txl ibl pgl bm nm vb (Src.own DFrac.discard)) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hcbk Hv
          · ipureintro; exact ⟨Hclean, Htx, Hbm3, bktClean_child W _ cl txl ibl pgl bm nm vb _ Hvb Hpnn (Or.inr rfl), rfl, rfl⟩
          · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
          icases Hown with ⟨Hown, %Hfr⟩
          have Hadd := txShape_add (GF := GF) γ W T { T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 } bl B nb cl (childRec txl ibl pgl bm nm vb (Src.own DFrac.discard)) vb HB Hfr Hent H16 rfl rfl rfl Htk
            ((bktToks_open γ W _ bl B cl nb vb Hclean HvOK Hnb Hent).trans
              (sep_mono .rfl (bktToks_child γ W txl ibl pgl bm nm vb (Src.own DFrac.discard))))
          unfold bOpen at Hadd
          ihave Hsh := Hadd $$ Hsh
          ispecialize HΦ $$ %cl %_
          iapply HΦ
          iframe
          ipureintro; refine ⟨wtxSub_add T _ bl B _ cl _ HB, Or.inr ?_⟩
          show ((<[cl := _]> (<[bl := _]> T.bs)) !! cl).isSome; rw [GMap.lookup_insert]; rfl
    · rw [decide_eq_false Heq, Bool.not_false]
      try wp_auto
      isimp only [wctx] at Hctx
      icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
      icases Hclose with ⟨Hclose, -⟩
      ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
      · ipureintro; exact ⟨Hclean, Htx, rfl⟩
      · unfold TxW_rest_root; simp only; rw [Hdb]; iframe; ipureintro; exact Htxn
      ihave Hsh := txShape_same γ W T (wtxUpd T _ bl B) bl B HB rfl $$ Hsh
      ispecialize HΦ $$ %(null) %_
      iapply HΦ
      iframe
      ipureintro; exact ⟨wtxSub_of_same _ _ (wtxSame_upd T _ bl B _ HB), Or.inl rfl⟩
  · obtain ⟨c, Hc⟩ : ∃ c, B.bm !! nb = some c := by
      cases h : B.bm !! nb with
      | none => rw [h] at Hc0; exact absurd rfl Hc0
      | some c => exact ⟨c, rfl⟩
    rw [Hc] at Hc0 ⊢
    simp only [Option.getD_some] at Hc0 ⊢
    rw [decide_eq_false Hc0, Bool.not_false]
    try wp_auto
    ihave Hbk : bktOwn (GF := GF) W bl B $$ [Hbv Hib Hnm Hbm Hpo Hns]
    · unfold bktOwn; iframe
    have Hcin : ((<[bl := B]> T.bs) !! c).isSome := by
      by_cases e : c = bl
      · subst e; rw [GMap.lookup_insert]; rfl
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact Hbmv _ c Hc
    icases Hclose with ⟨Hclose, -⟩
    ihave Hown := Hclose $$ %(T.t.stats') %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
    · ipureintro; exact ⟨Hclean, Htx, rfl⟩
    · unfold TxW_rest_root; simp only; rw [Hdb]; iframe; ipureintro; exact Htxn
    ihave Hsh := txShape_same γ W T (wtxUpd T _ bl B) bl B HB rfl $$ Hsh
    ispecialize HΦ $$ %(c) %_
    iapply HΦ
    iframe
    ipureintro; exact ⟨wtxSub_of_same _ _ (wtxSame_upd T _ bl B _ HB), Or.inr Hcin⟩

end proof

end bbolt
end EtcdGrove
end Perennial
