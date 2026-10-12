module
public import Spec.go_etcd_io.bbolt.Bucket__CreateBucketIfNotExists
public import Spec.go_etcd_io.bbolt.Bucket__openBucket_w
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.cloneBytes
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_w
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__node
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.Bucket__Bucket_w

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

theorem Bucket.CreateBucketIfNotExists.wp_proof (hLog : DB.Logger.spec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hCur : Bucket.Cursor.wspec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek.wspec (GF := GF) (hG := hG))
    (hWriteB : Bucket.write.spec (GF := GF) (hG := hG))
    (hNode : Cursor.node.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hBkt : Bucket.Bucket.wspec (GF := GF) (hG := hG))
    (hOpen : Bucket.openBucket.wspec (GF := GF) (hG := hG)) :
    Bucket.CreateBucketIfNotExists.spec (GF := GF) (hG := hG) := by
  intro W txl T bl key kb dk Hbl
  obtain ⟨B, HB⟩ := Option.isSome_iff_exists.1 Hbl
  wp_start as ⟨Hown, Hk⟩
  icases ownWriteTx_put_add W txl T bl B HB $$ Hown with ⟨%Hok, Hrest, Hmv, Hpm, Hb, Hv, Hrh, Hclose⟩
  obtain ⟨HvOK, Hwr, Hdb, Hdbn, Hpm0, H2, Hhwm, Hroot, Hbs⟩ := Hok
  obtain ⟨Htx, Hclean, Hbmv⟩ := Hbs bl B HB
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  ihave #Hby : (isPkgInit (PROP := IProp GF) pkg_id.bytes) $$ []
  · iPkgInit
  ihave %Hkl := ownSlice_len _ _ _ $$ Hk
  isimp only [TxW_rest_root] at Hrest
  icases Hrest with ⟨Hwritable, Hmanaged, Hdbf, Hmetaf, Hpages, Hstats, Hch, Hwf, %Htxn⟩
  isimp only [bktOwn] at Hb
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  isimp only [wView] at Hv
  icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  rw [Htx, Hdb]
  try wp_auto
  wp_apply hLog W.dbl DFrac.discard W.lg W.dl Hdbn $$ [Hlg Hdl] as Hlg'
  · iframe #
  have Hd : (if W.lg = interface.nil then discardIface W.dl else W.lg) = discardIface W.dl := by
    rcases Hlgv with h | h <;> rw [h] <;> simp [discardIface, interface.mkOk]
  rw [Hd]
  try wp_auto
  rw [Htx]
  try wp_auto
  rw [decide_eq_false Hdbn]
  try wp_auto
  rw [Hwr]
  try rw [Htx]
  try wp_auto
  by_cases Hk0 : key.len = W64 0
  · rw [decide_eq_true Hk0]
    try wp_auto
    icases bboltError_access errors.ErrBucketNameRequired (by simp [bboltErrorNames]) $$ Hei
      with ⟨%e, #He, %Hne⟩
    try wp_auto
    ihave Hbk : bktOwn (GF := GF) W bl B $$ [Hbv Hib Hnm Hbm Hpo Hns]
    · unfold bktOwn; iframe
    ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
    · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
    icases Hclose with ⟨Hclose, -⟩
    ihave Hown := Hclose $$ %(T.t.stats') %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv Hrh
    · ipureintro; exact ⟨Hclean, Htx, rfl⟩
    · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
    iapply HΦ
    iframe
    ipureintro; exact ⟨wtxSub_of_same _ _ (wtxSame_upd T _ bl B _ HB), Or.inl rfl⟩
  · rw [decide_eq_false Hk0]
    try wp_auto
    have Hkpos : 0 < kb.length := by
      rw [Hkl.1]; have := Hkl.2; word
    wp_apply hClone key kb dk $$ [Hk] as %nk ⟨Hnk, Hnkcap, Hk⟩
    · iframe
    try wp_auto
    ihave %Hbmnn := ownMap_not_nil _ _ _ $$ Hbm
    rw [decide_eq_false Hbmnn, Bool.not_false]
    try wp_auto
    wp_apply wp_bytes_to_string nk kb (DFrac.own 1) $$ [Hnk] as Hnk
    · iframe
    try wp_auto
    wp_apply wp_map_lookup1 $$ [Hbm] as Hbm
    · iframe
    try wp_auto
    by_cases Hc0 : (B.bm !! kb).getD (zero_val Loc) = null
    · rw [Hc0, decide_eq_true rfl, Bool.not_true]
      try wp_auto
      try rw [Htx]
      wp_apply hCur bl B.bv (DFrac.own 1) T.t.stats' $$ [Hbv Hstats] as %cl %s ⟨Hcl, Hs, Hcap, Hbv, Hstats⟩
      · rw [Htx]; iframe
      try wp_auto
      have HwOK : wctxOK W (uint.nat T.mv.pgid') bl B txl T.pm :=
        ⟨HvOK, Hclean, Htx, fun id _ => by rw [Hpm0]; rfl⟩
      wp_apply hSeek cl { bucket' := bl, stack' := s } [] W (uint.nat T.mv.pgid') bl B txl T.t.pages' T.pm
        (DFrac.own 1) nk kb (DFrac.own 1) rfl HwOK
        $$ [Hcl Hs Hcap Hbv Hib Hnm Hbm Hpo Hns Hdata Hpv Hfli Hpages Hpm Hdbf Hnk]
        as %cv' %path %k %v %f ⟨%Hsk, Hcl, Hs, Hcap, Hctx, Hnk⟩
      · isplitl [Hcl]
        · iframe
        iframe
        unfold wctx
        isplitl [Hbv Hib Hnm Hbm Hpo Hns]
        · unfold bktOwn; iframe
        isplitl [Hdata Hpv Hfli]
        · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
        iframe
      try wp_auto
      icases keySrc_acc W bl B txl T.t.pages' T.pm (DFrac.own 1) k HvOK.1 (kvSrc_key W _ B _ Hsk.2.2) $$ Hctx
        with ⟨%dq, %bs, Hkk, Hkback⟩
      wp_apply bytes.wp_Equal nk k (DFrac.own 1) dq kb bs $$ [Hnk Hkk] as ⟨Hnk, Hkk⟩
      · iframe
      ihave Hctx := Hkback $$ Hkk
      try wp_auto
      by_cases Heq : kb = bs
      · rw [decide_eq_true Heq]
        try wp_auto
        by_cases Hf : f &&& W32 1 = W32 0
        · rw [decide_eq_true Hf]
          try wp_auto
          icases bboltError_access errors.ErrIncompatibleValue (by simp [bboltErrorNames]) $$ Hei
            with ⟨%e, #He, %Hne⟩
          try wp_auto
          try rw [Htx]
          isimp only [wctx] at Hctx
          icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
          icases Hclose with ⟨Hclose, -⟩
          ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv Hrh
          · ipureintro; exact ⟨Hclean, Htx, rfl⟩
          · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
          iapply HΦ
          iframe
          ipureintro; exact ⟨wtxSub_of_same _ _ (wtxSame_upd T _ bl B _ HB), Or.inl rfl⟩
        · rw [decide_eq_false Hf]
          try wp_auto
          obtain ⟨vb, src, Hvb, Hsrc, Hacc⟩ : ∃ vb src, bvalOK W.pages (uint.nat T.mv.pgid') vb ∧
              (src = Src.view ∨ src = Src.own DFrac.discard) ∧
              ((src = Src.view ∧ inViewAt W v vb) ∨ (∃ (l : Loc) (r : NRec) (i : Nat)
                (it : internal.common.Inode) (w : WEntry), B.ns !! l = some r ∧ r.ins[i]? = some it ∧
                r.ws[i]? = some w ∧ it.value' = v ∧ w.value = vb ∧ w.vs = src)) := by
            rcases kvSrc_bkt W _ bl B Hclean HvOK k v f Hsk.2.2 Hf with ⟨vb, Hvb, Hin⟩ |
              ⟨l, r, i, it, w, Hr, Hit, Hw, Hv', Hvb, Hvs⟩
            · exact ⟨vb, Src.view, Hvb, Or.inl rfl, Or.inl ⟨rfl, Hin⟩⟩
            · exact ⟨w.value, w.vs, Hvb, Hvs, Or.inr ⟨l, r, i, it, w, Hr, Hit, Hw, Hv', rfl, rfl⟩⟩
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
          · rw [Htx]; iframe
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
            wp_apply wp_bytes_to_string nk kb (DFrac.own 1) $$ [Hnk] as Hnk
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
            ihave Hbk : bktOwn (GF := GF) W bl ({ B with bm := <[kb := cl]> B.bm }) $$ [Hbv Hib Hnm Hbm Hpo Hns]
            · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W ({ B with bm := <[kb := cl]> B.bm }) B rfl rfl rfl); iexact Hpo
            ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
            · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
            have Hbm3 : ∀ n c, ({ B with bm := <[kb := cl]> B.bm }).bm !! n = some c → c = cl ∨ (T.bs !! c).isSome := by
              intro n c h
              by_cases e : n = kb
              · subst e; simp only at h; rw [GMap.lookup_insert] at h; exact Or.inl (Option.some.inj h).symm
              · simp only at h; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr (Hbmv _ c h)
            icases Hclose with ⟨-, Hclose⟩
            ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %({ B with bm := <[kb := cl]> B.bm }) %cl %(childRec txl ibl pgl bm nm vb src) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hcbk Hv Hrh
            · ipureintro; exact ⟨Hclean, Htx, Hbm3, bktClean_child W _ cl txl ibl pgl bm nm vb _ Hvb Hpnn Hsrc, rfl, rfl⟩
            · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
            ispecialize HΦ $$ %cl %_ %_
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
            wp_apply wp_bytes_to_string nk kb (DFrac.own 1) $$ [Hnk] as Hnk
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
            ihave Hbk : bktOwn (GF := GF) W bl ({ B with bm := <[kb := cl]> B.bm }) $$ [Hbv Hib Hnm Hbm Hpo Hns]
            · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W ({ B with bm := <[kb := cl]> B.bm }) B rfl rfl rfl); iexact Hpo
            ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
            · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
            have Hbm3 : ∀ n c, ({ B with bm := <[kb := cl]> B.bm }).bm !! n = some c → c = cl ∨ (T.bs !! c).isSome := by
              intro n c h
              by_cases e : n = kb
              · subst e; simp only at h; rw [GMap.lookup_insert] at h; exact Or.inl (Option.some.inj h).symm
              · simp only at h; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr (Hbmv _ c h)
            icases Hclose with ⟨-, Hclose⟩
            ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %({ B with bm := <[kb := cl]> B.bm }) %cl %(childRec txl ibl pgl bm nm vb (Src.own DFrac.discard)) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hcbk Hv Hrh
            · ipureintro; exact ⟨Hclean, Htx, Hbm3, bktClean_child W _ cl txl ibl pgl bm nm vb _ Hvb Hpnn (Or.inr rfl), rfl, rfl⟩
            · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
            ispecialize HΦ $$ %cl %_ %_
            iapply HΦ
            iframe
            ipureintro; refine ⟨wtxSub_add T _ bl B _ cl _ HB, Or.inr ?_⟩
            show ((<[cl := _]> (<[bl := _]> T.bs)) !! cl).isSome; rw [GMap.lookup_insert]; rfl

      · rw [decide_eq_false Heq]
        try wp_auto
        ihave Hnil : (slice.nil ↦* ([] : List internal.common.Inode) : IProp GF) $$ []
        · iapply ownSlice_nil
        ihave Hdata0 : inodeData (GF := GF) [] [] [] (DFrac.own 1) $$ []
        · unfold inodeData; iapply BigSepL.bigSepL_nil.2; iempintro
        wp_apply hWriteB bucket_ptr _ (DFrac.own 1) (zero_val internal.common.InBucket) (DFrac.own 1)
          (⟨null, true, false, false, slice.nil, 0, null, slice.nil, slice.nil⟩ : node) (DFrac.own 1)
          [] (DFrac.own 1) [] [] (DFrac.own 1) (by simp) rfl rfl (by simp) (by simp [kvLen])
          (by simp [sizeFrom, kvLen]) (by simp) $$ [bucket «$v0» «$v1» Hnil Hdata0]
          as %val ⟨-, -, -, -, -, Hval, -⟩
        · simp only; iframe
        rw [show (zero_val internal.common.InBucket) = ⟨W64 0, W64 0⟩ from rfl]
        simp only
        rw [writtenBucket_empty]
        ihave Hval := ((ownSlice_dfractional (GF := GF) val emptyBV).dfractional_persist (DFrac.own 1)) $$ Hval
        imod Hval
        haveI := (ownSlice_dfractional (GF := GF) val emptyBV).dfractional_persistent
        icases Hval with #Hval
        try wp_auto
        by_cases hrl : bl = structFieldRef Tx go!"root" txl
        · rw [Htx]
          wp_apply hNode cl cv' path W (uint.nat T.mv.pgid') bl B txl _ T.t.pages' T.pm (DFrac.own 1)
            Hsk.1 HwOK Hsk.2.1 $$ [Hcl Hs Hctx Hstats] as %l %B' %st' ⟨Hcl, Hs, Hctx, Hstats, %Hn⟩
          · iframe
          obtain ⟨Hc', Hg', r, Hr, Hleaf⟩ := Hn
          obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, h11, -⟩ := Hc'.2.2.2.2.2.2.2.1 l r Hr
          have Htx' : B'.bv.tx' = txl := (bktGrows_tx B B' Hg').trans Htx
          isimp only [wctx] at Hctx
          icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
          isimp only [bktOwn] at Hbk
          icases Hbk with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
          icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
            (show Std.get? B'.ns l = some r from Hr)) $$ Hns with ⟨Hnd, Hnsback⟩
          isimp only [nodeOwn] at Hnd
          icases Hnd with ⟨Hn, Hins, Hicap, Hents, Hch2, Hchcap, Hkey⟩
          isimp only [wView] at Hv
          icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
          icases nodeBorrow W HvOK.1 r.ws r.ins W.q h5 $$ [Hpv Hents] with ⟨%es, %Hm, Hes, Hpback⟩
          · iframe
          ihave Hrest : TxW_rest_root (GF := GF) txl (DFrac.own 1) { T.t with stats' := st' } $$
            [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf]
          · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
          icases (TxW_rest_root_halves txl _).1 $$ Hrest with ⟨Hrest1, Hrest2⟩
          icases (pt_halves bl B'.bv).1 $$ Hbv with ⟨Hbv1, Hbv2⟩
          icases (slice_halves nk kb).1 $$ Hnk with ⟨Hnk1, Hnk2⟩
          have Hwl := wMatch_length Hm
          have Hil : r.ins.length = es.length := h2.trans Hwl
          try wp_auto
          ihave Hroot : structFieldRef Tx go!"root" txl ↦{DFrac.own halfQ} B'.bv $$ [Hbv2]
          · rw [← hrl]; iexact Hbv2
          ihave Htxp : txl ↦{DFrac.own halfQ} ({ T.t with stats' := st', root' := B'.bv } : Tx) $$ [Hroot Hrest1]
          · iapply (TxW_split_root txl (DFrac.own halfQ) _).2
            isimp only [TxW_rest_root] at Hrest1
            unfold TxW_rest_root; simp only
            iframe
          wp_apply hPut l r.nv r.ins es B'.bv (DFrac.own halfQ) ({ T.t with stats' := st', root' := B'.bv } : Tx) (DFrac.own halfQ) T.mv (DFrac.own 1)
            nk kb (DFrac.own halfQ) nk kb (DFrac.own halfQ) val emptyBV DFrac.discard (W64 0) (W32 1)
            ((wMatch_sorted _ _ Hm).2 h3) (by simp only [uint.nat] at H2; word) Hkpos Hkpos
            $$ [Hn Hins Hicap Hes Hbv1 Htxp Hmv Hnk1 Hnk2 Hval]
            as %idx %s' ⟨%Hidx, Hbv1, Htxp, Hmv, Hnk1, Hn, Hs', Hscap, Hes, Hold⟩
          · rw [h1, Htx']; iframe; iframe #
          try wp_auto
          have Hexeq : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) =
              decide (sint.nat idx < r.ws.length ∧ wKey r.ws (sint.nat idx) = kb) := by
            rw [← Hwl, wMatch_key _ _ Hm]
          ihave Hes := inodesOwn_unput r.ins es (sint.nat idx) _ (internal.common.Inode.mk (W32 1) (W64 0) nk val)
            (NodeEntry.mk (W32 1) (W64 0) kb emptyBV (DFrac.own halfQ) DFrac.discard) Hil $$ [Hes Hold]
          · iframe
          icases Hes with ⟨Hes, Hx⟩
          ihave Hes := Hpback $$ Hes
          icases Hes with ⟨Hpv, Hents⟩
          ihave Hwx : wOwn (GF := GF) W (internal.common.Inode.mk (W32 1) (W64 0) nk val) (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) $$ [Hx]
          · isimp only [inodeIs] at Hx
            icases Hx with ⟨-, Hxk, Hxv⟩
            unfold wOwn srcOwn; iframe; ipureintro; exact ⟨rfl, rfl⟩
          have Hhi : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) = true →
              sint.nat idx < r.ins.length := fun h => by rw [Hil]; exact (of_decide_eq_true h).1
          ihave Hents := bigSepL2_putList (fun it w => wOwn (GF := GF) W it w) r.ins r.ws (sint.nat idx) _
            (internal.common.Inode.mk (W32 1) (W64 0) nk val) (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) h2 Hhi $$ [Hents Hwx]
          · iframe
          obtain ⟨r', Hr'⟩ : ∃ r' : NRec, r' = { r with nv := { r.nv with inodes' := s' }, ins := putList r.ins (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (internal.common.Inode.mk (W32 1) (W64 0) nk val), ws := putList r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) } := ⟨_, rfl⟩
          ihave Hnd : nodeOwn (GF := GF) W l r' $$ [Hn Hs' Hscap Hents Hch2 Hchcap Hkey]
          · rw [Hr']; unfold nodeOwn; iframe
          ihave Hns := Hnsback $$ %r' Hnd
          try rw [Htx']
          icases (TxW_split_root txl _ _).1 $$ Htxp with ⟨Hroot, Hrest1⟩
          ihave Hrest : TxW_rest_root (GF := GF) txl (DFrac.own 1) { T.t with stats' := st' } $$ [Hrest1 Hrest2]
          · iapply (TxW_rest_root_halves txl _).2
            isimp only [TxW_rest_root] at Hrest1
            isimp only [TxW_rest_root] at Hrest2
            unfold TxW_rest_root; simp only
            iframe
          ihave Hbv2 : bl ↦{DFrac.own halfQ} B'.bv $$ [Hroot]
          · rw [hrl]; iexact Hroot
          ihave Hbv1 : bl ↦{DFrac.own halfQ} B'.bv $$ [Hbv1]
          · rw [← h1]; iexact Hbv1
          ihave Hbv := (pt_halves bl B'.bv).2 $$ [Hbv1 Hbv2]
          · iframe
          ihave Hrh : rootHalf (GF := GF) txl bl $$ []
          · unfold rootHalf; ileft; ipureintro; exact hrl
          try wp_auto
          ihave Hbk : bktOwn (GF := GF) W bl ({ B' with bv := { B'.bv with page' := null }, ns := <[l := r']> B'.ns }) $$ [Hbv Hib Hnm Hbm Hns]
          · unfold bktOwn pageOwn; simp only [↓reduceIte]; iframe; try (ipureintro; trivial)
          ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
          · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
          obtain ⟨Hle, Hlt, Hge⟩ := Hidx.2
          rw [← Hwl] at Hle
          have Hhex : ∀ w ∈ r'.ws, w = (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) ∨ w ∈ r.ws := fun w hw => by
            rw [Hr'] at hw; exact mem_putList _ _ _ _ _ hw
          have Hrn : B'.bv.rootNode' ≠ null := fun h => by rw [(Hc'.2.2.1 h).1] at Hr; cases Hr
          have Hcl1 := bktClean_leafSet W _ bl B' Hc' l r r' Hr Hleaf (by rw [Hr']; exact Hleaf) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']; simp only [length_putList, h2]) (by rw [Hr']; simp only; rw [Hexeq]; exact wsSorted_putList r.ws (sint.nat idx) (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) h3 Hle (fun k hk => by rw [← wMatch_key _ _ Hm]; exact Hlt k hk) (fun h => by rw [← wMatch_key _ _ Hm]; exact Hge (by rw [← Hwl]; exact h))) (fun w hw => by rcases Hhex w hw with rfl | hw; exact Hkpos; exact h4 w hw) (fun w hw => by rcases Hhex w hw with rfl | hw; exact ⟨by nofun, by nofun⟩; exact h5 w hw) (fun w hw hb => by rcases Hhex w hw with rfl | hw; exact ⟨bvalOK_empty _ _, Or.inr rfl⟩; exact h11 Hleaf w hw hb)
          have Hcl2 := bktClean_pageNil W _ bl _ Hcl1 Hrn
          icases Hclose with ⟨Hclose, -⟩
          ihave Hown := Hclose $$ %st' %({ B' with bv := { B'.bv with page' := null }, ns := <[l := r']> B'.ns }) [] Hrest Hmv Hpm Hbk Hv Hrh
          · ipureintro; exact ⟨Hcl2, Htx', Hg'.1⟩
          have Hbl' : ((wtxUpd T st' bl ({ B' with bv := { B'.bv with page' := null }, ns := <[l := r']> B'.ns })).bs !! bl).isSome := by
            show ((<[bl := _]> T.bs) !! bl).isSome; rw [GMap.lookup_insert]; rfl
          wp_apply hBkt W txl _ bl nk kb (DFrac.own halfQ) Hbl' $$ [Hown Hnk1] as %rb %T2 ⟨Hown, %Hsub, Hnk1⟩
          · iframe
          try wp_auto
          iapply HΦ
          iframe
          ipureintro
          exact ⟨wtxSub_trans _ _ _ (wtxSub_of_same _ _ (wtxSame_upd T _ bl B _ HB)) Hsub.1, Hsub.2⟩
        · rw [Htx]
          wp_apply hNode cl cv' path W (uint.nat T.mv.pgid') bl B txl _ T.t.pages' T.pm (DFrac.own 1)
            Hsk.1 HwOK Hsk.2.1 $$ [Hcl Hs Hctx Hstats] as %l %B' %st' ⟨Hcl, Hs, Hctx, Hstats, %Hn⟩
          · iframe
          obtain ⟨Hc', Hg', r, Hr, Hleaf⟩ := Hn
          obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, h11, -⟩ := Hc'.2.2.2.2.2.2.2.1 l r Hr
          have Htx' : B'.bv.tx' = txl := (bktGrows_tx B B' Hg').trans Htx
          isimp only [wctx] at Hctx
          icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
          isimp only [bktOwn] at Hbk
          icases Hbk with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
          icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
            (show Std.get? B'.ns l = some r from Hr)) $$ Hns with ⟨Hnd, Hnsback⟩
          isimp only [nodeOwn] at Hnd
          icases Hnd with ⟨Hn, Hins, Hicap, Hents, Hch2, Hchcap, Hkey⟩
          isimp only [wView] at Hv
          icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
          icases nodeBorrow W HvOK.1 r.ws r.ins W.q h5 $$ [Hpv Hents] with ⟨%es, %Hm, Hes, Hpback⟩
          · iframe
          ihave Hrest : TxW_rest_root (GF := GF) txl (DFrac.own 1) { T.t with stats' := st' } $$
            [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf]
          · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
          icases (TxW_rest_root_halves txl _).1 $$ Hrest with ⟨Hrest1, Hrest2⟩
          icases (pt_halves bl B'.bv).1 $$ Hbv with ⟨Hbv1, Hbv2⟩
          icases (slice_halves nk kb).1 $$ Hnk with ⟨Hnk1, Hnk2⟩
          have Hwl := wMatch_length Hm
          have Hil : r.ins.length = es.length := h2.trans Hwl
          try wp_auto
          isimp only [rootHalf] at Hrh
          icases Hrh with (%h | ⟨%rv, %hne, Hroot⟩)
          · exact absurd h hrl
          ihave Htxp : txl ↦{DFrac.own halfQ} ({ T.t with stats' := st', root' := rv } : Tx) $$ [Hroot Hrest1]
          · iapply (TxW_split_root txl (DFrac.own halfQ) _).2
            isimp only [TxW_rest_root] at Hrest1
            unfold TxW_rest_root; simp only
            iframe
          wp_apply hPut l r.nv r.ins es B'.bv (DFrac.own halfQ) ({ T.t with stats' := st', root' := rv } : Tx) (DFrac.own halfQ) T.mv (DFrac.own 1)
            nk kb (DFrac.own halfQ) nk kb (DFrac.own halfQ) val emptyBV DFrac.discard (W64 0) (W32 1)
            ((wMatch_sorted _ _ Hm).2 h3) (by simp only [uint.nat] at H2; word) Hkpos Hkpos
            $$ [Hn Hins Hicap Hes Hbv1 Htxp Hmv Hnk1 Hnk2 Hval]
            as %idx %s' ⟨%Hidx, Hbv1, Htxp, Hmv, Hnk1, Hn, Hs', Hscap, Hes, Hold⟩
          · rw [h1, Htx']; iframe; iframe #
          try wp_auto
          have Hexeq : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) =
              decide (sint.nat idx < r.ws.length ∧ wKey r.ws (sint.nat idx) = kb) := by
            rw [← Hwl, wMatch_key _ _ Hm]
          ihave Hes := inodesOwn_unput r.ins es (sint.nat idx) _ (internal.common.Inode.mk (W32 1) (W64 0) nk val)
            (NodeEntry.mk (W32 1) (W64 0) kb emptyBV (DFrac.own halfQ) DFrac.discard) Hil $$ [Hes Hold]
          · iframe
          icases Hes with ⟨Hes, Hx⟩
          ihave Hes := Hpback $$ Hes
          icases Hes with ⟨Hpv, Hents⟩
          ihave Hwx : wOwn (GF := GF) W (internal.common.Inode.mk (W32 1) (W64 0) nk val) (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) $$ [Hx]
          · isimp only [inodeIs] at Hx
            icases Hx with ⟨-, Hxk, Hxv⟩
            unfold wOwn srcOwn; iframe; ipureintro; exact ⟨rfl, rfl⟩
          have Hhi : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) = true →
              sint.nat idx < r.ins.length := fun h => by rw [Hil]; exact (of_decide_eq_true h).1
          ihave Hents := bigSepL2_putList (fun it w => wOwn (GF := GF) W it w) r.ins r.ws (sint.nat idx) _
            (internal.common.Inode.mk (W32 1) (W64 0) nk val) (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) h2 Hhi $$ [Hents Hwx]
          · iframe
          obtain ⟨r', Hr'⟩ : ∃ r' : NRec, r' = { r with nv := { r.nv with inodes' := s' }, ins := putList r.ins (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (internal.common.Inode.mk (W32 1) (W64 0) nk val), ws := putList r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) } := ⟨_, rfl⟩
          ihave Hnd : nodeOwn (GF := GF) W l r' $$ [Hn Hs' Hscap Hents Hch2 Hchcap Hkey]
          · rw [Hr']; unfold nodeOwn; iframe
          ihave Hns := Hnsback $$ %r' Hnd
          try rw [Htx']
          icases (TxW_split_root txl _ _).1 $$ Htxp with ⟨Hroot, Hrest1⟩
          ihave Hrest : TxW_rest_root (GF := GF) txl (DFrac.own 1) { T.t with stats' := st' } $$ [Hrest1 Hrest2]
          · iapply (TxW_rest_root_halves txl _).2
            isimp only [TxW_rest_root] at Hrest1
            isimp only [TxW_rest_root] at Hrest2
            unfold TxW_rest_root; simp only
            iframe
          ihave Hbv1 : bl ↦{DFrac.own halfQ} B'.bv $$ [Hbv1]
          · rw [← h1]; iexact Hbv1
          ihave Hbv := (pt_halves bl B'.bv).2 $$ [Hbv1 Hbv2]
          · iframe
          ihave Hrh : rootHalf (GF := GF) txl bl $$ [Hroot]
          · unfold rootHalf; iright; iexists rv; iframe; ipureintro; exact hne
          try wp_auto
          ihave Hbk : bktOwn (GF := GF) W bl ({ B' with bv := { B'.bv with page' := null }, ns := <[l := r']> B'.ns }) $$ [Hbv Hib Hnm Hbm Hns]
          · unfold bktOwn pageOwn; simp only [↓reduceIte]; iframe; try (ipureintro; trivial)
          ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
          · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
          obtain ⟨Hle, Hlt, Hge⟩ := Hidx.2
          rw [← Hwl] at Hle
          have Hhex : ∀ w ∈ r'.ws, w = (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) ∨ w ∈ r.ws := fun w hw => by
            rw [Hr'] at hw; exact mem_putList _ _ _ _ _ hw
          have Hrn : B'.bv.rootNode' ≠ null := fun h => by rw [(Hc'.2.2.1 h).1] at Hr; cases Hr
          have Hcl1 := bktClean_leafSet W _ bl B' Hc' l r r' Hr Hleaf (by rw [Hr']; exact Hleaf) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']; simp only [length_putList, h2]) (by rw [Hr']; simp only; rw [Hexeq]; exact wsSorted_putList r.ws (sint.nat idx) (⟨W32 1, W64 0, kb, emptyBV, Src.own (DFrac.own halfQ), Src.own DFrac.discard⟩ : WEntry) h3 Hle (fun k hk => by rw [← wMatch_key _ _ Hm]; exact Hlt k hk) (fun h => by rw [← wMatch_key _ _ Hm]; exact Hge (by rw [← Hwl]; exact h))) (fun w hw => by rcases Hhex w hw with rfl | hw; exact Hkpos; exact h4 w hw) (fun w hw => by rcases Hhex w hw with rfl | hw; exact ⟨by nofun, by nofun⟩; exact h5 w hw) (fun w hw hb => by rcases Hhex w hw with rfl | hw; exact ⟨bvalOK_empty _ _, Or.inr rfl⟩; exact h11 Hleaf w hw hb)
          have Hcl2 := bktClean_pageNil W _ bl _ Hcl1 Hrn
          icases Hclose with ⟨Hclose, -⟩
          ihave Hown := Hclose $$ %st' %({ B' with bv := { B'.bv with page' := null }, ns := <[l := r']> B'.ns }) [] Hrest Hmv Hpm Hbk Hv Hrh
          · ipureintro; exact ⟨Hcl2, Htx', Hg'.1⟩
          have Hbl' : ((wtxUpd T st' bl ({ B' with bv := { B'.bv with page' := null }, ns := <[l := r']> B'.ns })).bs !! bl).isSome := by
            show ((<[bl := _]> T.bs) !! bl).isSome; rw [GMap.lookup_insert]; rfl
          wp_apply hBkt W txl _ bl nk kb (DFrac.own halfQ) Hbl' $$ [Hown Hnk1] as %rb %T2 ⟨Hown, %Hsub, Hnk1⟩
          · iframe
          try wp_auto
          iapply HΦ
          iframe
          ipureintro
          exact ⟨wtxSub_trans _ _ _ (wtxSub_of_same _ _ (wtxSame_upd T _ bl B _ HB)) Hsub.1, Hsub.2⟩

    · obtain ⟨c, Hc⟩ : ∃ c, B.bm !! kb = some c := by
        cases h : B.bm !! kb with
        | none => rw [h] at Hc0; exact absurd rfl Hc0
        | some c => exact ⟨c, rfl⟩
      rw [Hc] at Hc0 ⊢
      simp only [Option.getD_some] at Hc0 ⊢
      try rw [decide_eq_false Hc0]
      try rw [Bool.not_false]
      try wp_auto
      ihave Hbk : bktOwn (GF := GF) W bl B $$ [Hbv Hib Hnm Hbm Hpo Hns]
      · unfold bktOwn; iframe
      ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
      · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
      have Hcin : ((<[bl := B]> T.bs) !! c).isSome := by
        by_cases e : c = bl
        · subst e; rw [GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact (Hbs bl B HB).2.2 _ c Hc
      icases Hclose with ⟨Hclose, -⟩
      ihave Hown := Hclose $$ %(T.t.stats') %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv Hrh
      · ipureintro; exact ⟨Hclean, Htx, rfl⟩
      · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
      iapply HΦ
      iframe
      ipureintro; exact ⟨wtxSub_of_same _ _ (wtxSame_upd T _ bl B _ HB), Or.inr Hcin⟩

end proof

end bbolt
end EtcdGrove
end Perennial
