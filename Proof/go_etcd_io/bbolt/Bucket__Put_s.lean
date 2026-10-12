module
public import Spec.go_etcd_io.bbolt.Bucket__Put_s
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.Bucket__Writable_w
public import Spec.go_etcd_io.bbolt.cloneBytes
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_w
public import Spec.go_etcd_io.bbolt.Cursor__seek_s
public import Spec.go_etcd_io.bbolt.Cursor__node_s
public import Spec.go_etcd_io.bbolt.node__put
public import Proof.go_etcd_io.bbolt.ShapeLeaf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Put.wp_sproof (hLog : DB.Logger.spec (GF := GF) (hG := hG))
    (hWr : Bucket.Writable.wspec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hCur : Bucket.Cursor.wspec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek.sspec (GF := GF) (hG := hG))
    (hNode : Cursor.node.sspec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG)) :
    Bucket.Put.sspec (GF := GF) (hG := hG) := by
  intro γ W txl T bl key value kb vb dk dv Hbl
  obtain ⟨B, HB⟩ := Option.isSome_iff_exists.1 Hbl
  wp_start as ⟨Hown, Hk, Hval, Hsh⟩
  icases ownWriteTx_put_acc W txl T bl B HB $$ Hown with ⟨%Hok, Hrest, Hmv, Hpm, Hb, Hv, Hrh, Hclose⟩
  obtain ⟨HvOK, Hwr, Hdb, Hdbn, Hpm0, H2, Hhwm, Hroot, Hbs⟩ := Hok
  obtain ⟨Htx, Hclean, -⟩ := Hbs bl B HB
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  ihave #Hby : (isPkgInit (PROP := IProp GF) pkg_id.bytes) $$ []
  · iPkgInit
  ihave %Hkl := ownSlice_len _ _ _ $$ Hk
  ihave %Hvl := ownSlice_len _ _ _ $$ Hval
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
  try rw [Htx]
  try wp_auto
  rw [decide_eq_false Hdbn]
  try wp_auto
  wp_apply hWr bl B.bv (DFrac.own 1) T.t.writable' (DFrac.own 1) $$ [Hbv Hwritable] as ⟨Hbv, Hwritable⟩
  · rw [Htx]; iframe
  rw [Hwr]
  try wp_auto
  try rw [Htx]
  by_cases Hk0 : key.len = W64 0
  · rw [decide_eq_true Hk0]
    try wp_auto
    icases bboltError_access errors.ErrKeyRequired (by simp [bboltErrorNames]) $$ Hei
      with ⟨%e, #He, %Hne⟩
    try wp_auto
    ihave Hbk : bktOwn (GF := GF) W bl B $$ [Hbv Hib Hnm Hbm Hpo Hns]
    · unfold bktOwn; iframe
    ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
    · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
    ihave Hsh := txShape_same γ W T (wtxUpd T T.t.stats' bl B) bl B HB rfl $$ Hsh
    ihave Hown := Hclose $$ %(T.t.stats') %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv Hrh
    · ipureintro; exact ⟨Hclean, Htx, rfl⟩
    · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact wtxSame_upd T _ bl B _ HB
    iright; iframe; ipureintro; obtain ⟨t, p, rfl⟩ := Hne; exact fun h => by cases h
  · rw [decide_eq_false Hk0]
    try wp_auto
    by_cases Hkt : sint.Z (W64 32768) < sint.Z key.len
    · rw [decide_eq_true Hkt]
      try wp_auto
      icases bboltError_access errors.ErrKeyTooLarge (by simp [bboltErrorNames]) $$ Hei
        with ⟨%e, #He, %Hne⟩
      try wp_auto
      ihave Hbk : bktOwn (GF := GF) W bl B $$ [Hbv Hib Hnm Hbm Hpo Hns]
      · unfold bktOwn; iframe
      ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
      · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
      ihave Hsh := txShape_same γ W T (wtxUpd T T.t.stats' bl B) bl B HB rfl $$ Hsh
      ihave Hown := Hclose $$ %(T.t.stats') %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv Hrh
      · ipureintro; exact ⟨Hclean, Htx, rfl⟩
      · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact wtxSame_upd T _ bl B _ HB
      iright; iframe; ipureintro; obtain ⟨t, p, rfl⟩ := Hne; exact fun h => by cases h
    · rw [decide_eq_false Hkt]
      try wp_auto
      have Hkpos : 0 < kb.length := by
        rw [Hkl.1]; have := Hkl.2; word
      by_cases Hvt : sint.Z (W64 2147483646) < sint.Z value.len
      · rw [decide_eq_true Hvt]
        try wp_auto
        icases bboltError_access errors.ErrValueTooLarge (by simp [bboltErrorNames]) $$ Hei
          with ⟨%e, #He, %Hne⟩
        try wp_auto
        ihave Hbk : bktOwn (GF := GF) W bl B $$ [Hbv Hib Hnm Hbm Hpo Hns]
        · unfold bktOwn; iframe
        ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
        · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
        ihave Hsh := txShape_same γ W T (wtxUpd T T.t.stats' bl B) bl B HB rfl $$ Hsh
        ihave Hown := Hclose $$ %(T.t.stats') %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv Hrh
        · ipureintro; exact ⟨Hclean, Htx, rfl⟩
        · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
        iapply HΦ
        iframe
        isplitr
        · ipureintro; exact wtxSame_upd T _ bl B _ HB
        iright; iframe; ipureintro; obtain ⟨t, p, rfl⟩ := Hne; exact fun h => by cases h
      · rw [decide_eq_false Hvt]
        try wp_auto
        wp_apply hClone key kb dk $$ [Hk] as %nk ⟨Hnk, Hnkcap, Hk⟩
        · iframe
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
        obtain ⟨Hsk1, Hsk2, -, Hkr, -, kbs, Hks, -, Hpk⟩ := Hsk
        try wp_auto
        icases keySrcIs_acc W bl B txl T.t.pages' T.pm (DFrac.own 1) k kbs HvOK.1 Hks $$ Hctx
          with ⟨%dq, Hkk, Hkback⟩
        wp_apply bytes.wp_Equal nk k (DFrac.own 1) dq kb kbs $$ [Hnk Hkk] as ⟨Hnk, Hkk⟩
        · iframe
        ihave Hctx := Hkback $$ Hkk
        try wp_auto
        by_cases Heq : kb = kbs
        · rw [decide_eq_true Heq]
          try wp_auto
          by_cases Hf : f &&& W32 1 = W32 0
          · rw [decide_eq_true Hf]
            try wp_auto
            by_cases hrl : bl = structFieldRef Tx go!"root" txl
            · rw [Htx]
              icases txShape_open γ W T bl B HB $$ Hsh with ⟨Hbsh, Hfr, -⟩
              wp_apply hNode γ cl cv' path W (uint.nat T.mv.pgid') bl B txl _ T.t.pages' T.pm (DFrac.own 1)
                Hsk1 HwOK Hsk2 $$ [Hcl Hs Hctx Hstats Hbsh] as %l %B' %st' ⟨Hcl, Hs, Hctx, Hstats, Hbsh, %Hn⟩
              · iframe
              obtain ⟨Hc', Hg', ⟨r, Hr, Hleaf⟩, Hent, Hroute, Hpath⟩ := Hn
              obtain ⟨bnd, Hbkb, Hkin⟩ := Hroute kb Hkr
              have HP := Hpath kb _ Hpk r Hr
              have Hrn : B'.bv.rootNode' = null → B.bv.rootNode' = null := fun h => by
                rw [(Hc'.2.2.1 h).1] at Hr; cases Hr
              isimp only [bktShape] at Hbsh
              icases Hbsh with ⟨Htk, -⟩
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
                nk kb (DFrac.own halfQ) nk kb (DFrac.own halfQ) value vb dv (W64 0) (W32 0)
                ((wMatch_sorted _ _ Hm).2 h3) (by simp only [uint.nat] at H2; word) Hkpos Hkpos
                $$ [Hn Hins Hicap Hes Hbv1 Htxp Hmv Hnk1 Hnk2 Hval]
                as %idx %s' ⟨%Hidx, Hbv1, Htxp, Hmv, Hnk1, Hn, Hs', Hscap, Hes, Hold⟩
              · rw [h1, Htx']; iframe
              try wp_auto
              have Hexeq : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) =
                  decide (sint.nat idx < r.ws.length ∧ wKey r.ws (sint.nat idx) = kb) := by
                rw [← Hwl, wMatch_key _ _ Hm]
              ihave Hes := inodesOwn_unput r.ins es (sint.nat idx) _ (internal.common.Inode.mk (W32 0) (W64 0) nk value)
                (NodeEntry.mk (W32 0) (W64 0) kb vb (DFrac.own halfQ) dv) Hil $$ [Hes Hold]
              · iframe
              icases Hes with ⟨Hes, Hx⟩
              ihave Hes := Hpback $$ Hes
              icases Hes with ⟨Hpv, Hents⟩
              ihave Hwx : wOwn (GF := GF) W (internal.common.Inode.mk (W32 0) (W64 0) nk value) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) $$ [Hx]
              · isimp only [inodeIs] at Hx
                icases Hx with ⟨-, Hxk, Hxv⟩
                unfold wOwn srcOwn; iframe; ipureintro; exact ⟨rfl, rfl⟩
              have Hhi : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) = true →
                  sint.nat idx < r.ins.length := fun h => by rw [Hil]; exact (of_decide_eq_true h).1
              ihave Hents := bigSepL2_putList (fun it w => wOwn (GF := GF) W it w) r.ins r.ws (sint.nat idx) _
                (internal.common.Inode.mk (W32 0) (W64 0) nk value) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) h2 Hhi $$ [Hents Hwx]
              · iframe
              obtain ⟨r', Hr'⟩ : ∃ r' : NRec, r' = { r with nv := { r.nv with inodes' := s' }, ins := putList r.ins (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (internal.common.Inode.mk (W32 0) (W64 0) nk value), ws := putList r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) } := ⟨_, rfl⟩
              ihave Hnd : nodeOwn (GF := GF) W l r' $$ [Hn Hs' Hscap Hents Hch2 Hchcap Hkey]
              · rw [Hr']; unfold nodeOwn; iframe
              ihave Hns := Hnsback $$ %r' Hnd
              obtain ⟨A, D, C, hws, hws0, hD0⟩ := putList_split r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)
                (fun h => by rw [Hwl]; exact (of_decide_eq_true h).1)
              have hws' : r'.ws = A ++ [(⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)] ++ C := by rw [Hr']; exact hws0
              have hD : ∀ w ∈ D, ¬ isBktFlag w.flags := by
                intro w hw hb
                obtain ⟨hex, hw'⟩ := hD0 w hw
                have hkw : wKey r.ws (sint.nat idx) = kb := by
                  rw [← wMatch_key _ _ Hm]; exact (of_decide_eq_true hex).2
                have hh := pathKey_at r.ws (sint.nat idx) w kb kbs f hw' hkw HP
                first | exact Heq hh.2.symm | (rw [hh.1] at hb; exact hb Hf)
              have hE : ∀ w ∈ [(⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)], keyIn (bnd l).1 (bnd l).2 w.key ∧ ¬ isBktFlag w.flags := by
                intro w hw
                simp only [List.mem_singleton] at hw
                subst hw
                exact ⟨Hkin, fun hb => hb (by show (W32 0 &&& W32 1 : w32) = W32 0; decide)⟩
              have e1 : r'.nv.isLeaf' = true := by rw [Hr']; exact Hleaf
              ihave Htk := bktToks_leafOp γ W (uint.nat T.mv.pgid') bl B' Hc' l r r' Hr Hleaf e1
                (by rw [Hr']) A D C _ hws hws' (fun w hw => (hE w hw).2) $$ Htk
              ihave Hsh := txShape_close γ W T (wtxUpd T st' bl { B' with ns := <[l := r']> B'.ns }) bl B
                { B' with ns := <[l := r']> B'.ns } HB rfl Hg'.2.1 Hg'.1 Hrn
                (fun k v h => entryIn_leafOp W B' l r r' Hr Hleaf e1 A D C _ hws hws' hD k v (Hent k v h))
                ⟨bnd, bktKeysB_leafOp W _ bl B' Hc' bnd Hbkb l r r' Hr Hleaf A D C _ hws hws' hE e1
                  (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr'])
                  (fun _ => by rw [hws']; simp; omega)⟩ $$ [Hfr Htk]
              · iframe
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
              ihave Hbk : bktOwn (GF := GF) W bl { B' with ns := <[l := r']> B'.ns } $$ [Hbv Hib Hnm Hbm Hpo Hns]
              · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W { B' with ns := <[l := r']> B'.ns } B' rfl rfl rfl); iexact Hpo
              ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
              · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
              obtain ⟨Hle, Hlt, Hge⟩ := Hidx.2
              rw [← Hwl] at Hle
              have Hhex : ∀ w ∈ r'.ws, w = (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) ∨ w ∈ r.ws := fun w hw => by
                rw [Hr'] at hw; exact mem_putList _ _ _ _ _ hw
              ihave Hown := Hclose $$ %st' %({ B' with ns := <[l := r']> B'.ns }) [] Hrest Hmv Hpm Hbk Hv Hrh
              · ipureintro; exact ⟨bktClean_leafSet W _ bl B' Hc' l r r' Hr Hleaf (by rw [Hr']; exact Hleaf) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']; simp only [length_putList, h2]) (by rw [Hr']; simp only; rw [Hexeq]; exact wsSorted_putList r.ws (sint.nat idx) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) h3 Hle (fun k hk => by rw [← wMatch_key _ _ Hm]; exact Hlt k hk) (fun h => by rw [← wMatch_key _ _ Hm]; exact Hge (by rw [← Hwl]; exact h))) (fun w hw => by rcases Hhex w hw with rfl | hw; exact Hkpos; exact h4 w hw) (fun w hw => by rcases Hhex w hw with rfl | hw; exact ⟨by nofun, by nofun⟩; exact h5 w hw) (fun w hw hb => by rcases Hhex w hw with rfl | hw; exact (hb (by show (W32 0 &&& W32 1 : w32) = W32 0; decide)).elim; exact h11 Hleaf w hw hb), Htx', Hg'.1⟩
              iapply HΦ
              iframe
              isplitr
              · ipureintro; exact wtxSame_upd T _ bl B _ HB
              ileft; ipureintro; rfl
            · rw [Htx]
              icases txShape_open γ W T bl B HB $$ Hsh with ⟨Hbsh, Hfr, -⟩
              wp_apply hNode γ cl cv' path W (uint.nat T.mv.pgid') bl B txl _ T.t.pages' T.pm (DFrac.own 1)
                Hsk1 HwOK Hsk2 $$ [Hcl Hs Hctx Hstats Hbsh] as %l %B' %st' ⟨Hcl, Hs, Hctx, Hstats, Hbsh, %Hn⟩
              · iframe
              obtain ⟨Hc', Hg', ⟨r, Hr, Hleaf⟩, Hent, Hroute, Hpath⟩ := Hn
              obtain ⟨bnd, Hbkb, Hkin⟩ := Hroute kb Hkr
              have HP := Hpath kb _ Hpk r Hr
              have Hrn : B'.bv.rootNode' = null → B.bv.rootNode' = null := fun h => by
                rw [(Hc'.2.2.1 h).1] at Hr; cases Hr
              isimp only [bktShape] at Hbsh
              icases Hbsh with ⟨Htk, -⟩
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
                nk kb (DFrac.own halfQ) nk kb (DFrac.own halfQ) value vb dv (W64 0) (W32 0)
                ((wMatch_sorted _ _ Hm).2 h3) (by simp only [uint.nat] at H2; word) Hkpos Hkpos
                $$ [Hn Hins Hicap Hes Hbv1 Htxp Hmv Hnk1 Hnk2 Hval]
                as %idx %s' ⟨%Hidx, Hbv1, Htxp, Hmv, Hnk1, Hn, Hs', Hscap, Hes, Hold⟩
              · rw [h1, Htx']; iframe
              try wp_auto
              have Hexeq : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) =
                  decide (sint.nat idx < r.ws.length ∧ wKey r.ws (sint.nat idx) = kb) := by
                rw [← Hwl, wMatch_key _ _ Hm]
              ihave Hes := inodesOwn_unput r.ins es (sint.nat idx) _ (internal.common.Inode.mk (W32 0) (W64 0) nk value)
                (NodeEntry.mk (W32 0) (W64 0) kb vb (DFrac.own halfQ) dv) Hil $$ [Hes Hold]
              · iframe
              icases Hes with ⟨Hes, Hx⟩
              ihave Hes := Hpback $$ Hes
              icases Hes with ⟨Hpv, Hents⟩
              ihave Hwx : wOwn (GF := GF) W (internal.common.Inode.mk (W32 0) (W64 0) nk value) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) $$ [Hx]
              · isimp only [inodeIs] at Hx
                icases Hx with ⟨-, Hxk, Hxv⟩
                unfold wOwn srcOwn; iframe; ipureintro; exact ⟨rfl, rfl⟩
              have Hhi : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) = true →
                  sint.nat idx < r.ins.length := fun h => by rw [Hil]; exact (of_decide_eq_true h).1
              ihave Hents := bigSepL2_putList (fun it w => wOwn (GF := GF) W it w) r.ins r.ws (sint.nat idx) _
                (internal.common.Inode.mk (W32 0) (W64 0) nk value) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) h2 Hhi $$ [Hents Hwx]
              · iframe
              obtain ⟨r', Hr'⟩ : ∃ r' : NRec, r' = { r with nv := { r.nv with inodes' := s' }, ins := putList r.ins (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (internal.common.Inode.mk (W32 0) (W64 0) nk value), ws := putList r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) } := ⟨_, rfl⟩
              ihave Hnd : nodeOwn (GF := GF) W l r' $$ [Hn Hs' Hscap Hents Hch2 Hchcap Hkey]
              · rw [Hr']; unfold nodeOwn; iframe
              ihave Hns := Hnsback $$ %r' Hnd
              obtain ⟨A, D, C, hws, hws0, hD0⟩ := putList_split r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)
                (fun h => by rw [Hwl]; exact (of_decide_eq_true h).1)
              have hws' : r'.ws = A ++ [(⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)] ++ C := by rw [Hr']; exact hws0
              have hD : ∀ w ∈ D, ¬ isBktFlag w.flags := by
                intro w hw hb
                obtain ⟨hex, hw'⟩ := hD0 w hw
                have hkw : wKey r.ws (sint.nat idx) = kb := by
                  rw [← wMatch_key _ _ Hm]; exact (of_decide_eq_true hex).2
                have hh := pathKey_at r.ws (sint.nat idx) w kb kbs f hw' hkw HP
                first | exact Heq hh.2.symm | (rw [hh.1] at hb; exact hb Hf)
              have hE : ∀ w ∈ [(⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)], keyIn (bnd l).1 (bnd l).2 w.key ∧ ¬ isBktFlag w.flags := by
                intro w hw
                simp only [List.mem_singleton] at hw
                subst hw
                exact ⟨Hkin, fun hb => hb (by show (W32 0 &&& W32 1 : w32) = W32 0; decide)⟩
              have e1 : r'.nv.isLeaf' = true := by rw [Hr']; exact Hleaf
              ihave Htk := bktToks_leafOp γ W (uint.nat T.mv.pgid') bl B' Hc' l r r' Hr Hleaf e1
                (by rw [Hr']) A D C _ hws hws' (fun w hw => (hE w hw).2) $$ Htk
              ihave Hsh := txShape_close γ W T (wtxUpd T st' bl { B' with ns := <[l := r']> B'.ns }) bl B
                { B' with ns := <[l := r']> B'.ns } HB rfl Hg'.2.1 Hg'.1 Hrn
                (fun k v h => entryIn_leafOp W B' l r r' Hr Hleaf e1 A D C _ hws hws' hD k v (Hent k v h))
                ⟨bnd, bktKeysB_leafOp W _ bl B' Hc' bnd Hbkb l r r' Hr Hleaf A D C _ hws hws' hE e1
                  (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr'])
                  (fun _ => by rw [hws']; simp; omega)⟩ $$ [Hfr Htk]
              · iframe
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
              ihave Hbk : bktOwn (GF := GF) W bl { B' with ns := <[l := r']> B'.ns } $$ [Hbv Hib Hnm Hbm Hpo Hns]
              · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W { B' with ns := <[l := r']> B'.ns } B' rfl rfl rfl); iexact Hpo
              ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
              · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
              obtain ⟨Hle, Hlt, Hge⟩ := Hidx.2
              rw [← Hwl] at Hle
              have Hhex : ∀ w ∈ r'.ws, w = (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) ∨ w ∈ r.ws := fun w hw => by
                rw [Hr'] at hw; exact mem_putList _ _ _ _ _ hw
              ihave Hown := Hclose $$ %st' %({ B' with ns := <[l := r']> B'.ns }) [] Hrest Hmv Hpm Hbk Hv Hrh
              · ipureintro; exact ⟨bktClean_leafSet W _ bl B' Hc' l r r' Hr Hleaf (by rw [Hr']; exact Hleaf) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']; simp only [length_putList, h2]) (by rw [Hr']; simp only; rw [Hexeq]; exact wsSorted_putList r.ws (sint.nat idx) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) h3 Hle (fun k hk => by rw [← wMatch_key _ _ Hm]; exact Hlt k hk) (fun h => by rw [← wMatch_key _ _ Hm]; exact Hge (by rw [← Hwl]; exact h))) (fun w hw => by rcases Hhex w hw with rfl | hw; exact Hkpos; exact h4 w hw) (fun w hw => by rcases Hhex w hw with rfl | hw; exact ⟨by nofun, by nofun⟩; exact h5 w hw) (fun w hw hb => by rcases Hhex w hw with rfl | hw; exact (hb (by show (W32 0 &&& W32 1 : w32) = W32 0; decide)).elim; exact h11 Hleaf w hw hb), Htx', Hg'.1⟩
              iapply HΦ
              iframe
              isplitr
              · ipureintro; exact wtxSame_upd T _ bl B _ HB
              ileft; ipureintro; rfl
          · rw [decide_eq_false Hf]
            try wp_auto
            icases bboltError_access errors.ErrIncompatibleValue (by simp [bboltErrorNames]) $$ Hei
              with ⟨%e, #He, %Hne⟩
            try wp_auto
            try rw [Htx]
            isimp only [wctx] at Hctx
            icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
            ihave Hsh := txShape_same γ W T (wtxUpd T { T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 } bl B) bl B HB rfl $$ Hsh
            ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv Hrh
            · ipureintro; exact ⟨Hclean, Htx, rfl⟩
            · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
            iapply HΦ
            iframe
            isplitr
            · ipureintro; exact wtxSame_upd T _ bl B _ HB
            iright; iframe; ipureintro; obtain ⟨t, p, rfl⟩ := Hne; exact fun h => by cases h
        · rw [decide_eq_false Heq]
          try wp_auto
          by_cases hrl : bl = structFieldRef Tx go!"root" txl
          · rw [Htx]
            icases txShape_open γ W T bl B HB $$ Hsh with ⟨Hbsh, Hfr, -⟩
            wp_apply hNode γ cl cv' path W (uint.nat T.mv.pgid') bl B txl _ T.t.pages' T.pm (DFrac.own 1)
              Hsk1 HwOK Hsk2 $$ [Hcl Hs Hctx Hstats Hbsh] as %l %B' %st' ⟨Hcl, Hs, Hctx, Hstats, Hbsh, %Hn⟩
            · iframe
            obtain ⟨Hc', Hg', ⟨r, Hr, Hleaf⟩, Hent, Hroute, Hpath⟩ := Hn
            obtain ⟨bnd, Hbkb, Hkin⟩ := Hroute kb Hkr
            have HP := Hpath kb _ Hpk r Hr
            have Hrn : B'.bv.rootNode' = null → B.bv.rootNode' = null := fun h => by
              rw [(Hc'.2.2.1 h).1] at Hr; cases Hr
            isimp only [bktShape] at Hbsh
            icases Hbsh with ⟨Htk, -⟩
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
              nk kb (DFrac.own halfQ) nk kb (DFrac.own halfQ) value vb dv (W64 0) (W32 0)
              ((wMatch_sorted _ _ Hm).2 h3) (by simp only [uint.nat] at H2; word) Hkpos Hkpos
              $$ [Hn Hins Hicap Hes Hbv1 Htxp Hmv Hnk1 Hnk2 Hval]
              as %idx %s' ⟨%Hidx, Hbv1, Htxp, Hmv, Hnk1, Hn, Hs', Hscap, Hes, Hold⟩
            · rw [h1, Htx']; iframe
            try wp_auto
            have Hexeq : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) =
                decide (sint.nat idx < r.ws.length ∧ wKey r.ws (sint.nat idx) = kb) := by
              rw [← Hwl, wMatch_key _ _ Hm]
            ihave Hes := inodesOwn_unput r.ins es (sint.nat idx) _ (internal.common.Inode.mk (W32 0) (W64 0) nk value)
              (NodeEntry.mk (W32 0) (W64 0) kb vb (DFrac.own halfQ) dv) Hil $$ [Hes Hold]
            · iframe
            icases Hes with ⟨Hes, Hx⟩
            ihave Hes := Hpback $$ Hes
            icases Hes with ⟨Hpv, Hents⟩
            ihave Hwx : wOwn (GF := GF) W (internal.common.Inode.mk (W32 0) (W64 0) nk value) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) $$ [Hx]
            · isimp only [inodeIs] at Hx
              icases Hx with ⟨-, Hxk, Hxv⟩
              unfold wOwn srcOwn; iframe; ipureintro; exact ⟨rfl, rfl⟩
            have Hhi : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) = true →
                sint.nat idx < r.ins.length := fun h => by rw [Hil]; exact (of_decide_eq_true h).1
            ihave Hents := bigSepL2_putList (fun it w => wOwn (GF := GF) W it w) r.ins r.ws (sint.nat idx) _
              (internal.common.Inode.mk (W32 0) (W64 0) nk value) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) h2 Hhi $$ [Hents Hwx]
            · iframe
            obtain ⟨r', Hr'⟩ : ∃ r' : NRec, r' = { r with nv := { r.nv with inodes' := s' }, ins := putList r.ins (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (internal.common.Inode.mk (W32 0) (W64 0) nk value), ws := putList r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) } := ⟨_, rfl⟩
            ihave Hnd : nodeOwn (GF := GF) W l r' $$ [Hn Hs' Hscap Hents Hch2 Hchcap Hkey]
            · rw [Hr']; unfold nodeOwn; iframe
            ihave Hns := Hnsback $$ %r' Hnd
            obtain ⟨A, D, C, hws, hws0, hD0⟩ := putList_split r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)
              (fun h => by rw [Hwl]; exact (of_decide_eq_true h).1)
            have hws' : r'.ws = A ++ [(⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)] ++ C := by rw [Hr']; exact hws0
            have hD : ∀ w ∈ D, ¬ isBktFlag w.flags := by
              intro w hw hb
              obtain ⟨hex, hw'⟩ := hD0 w hw
              have hkw : wKey r.ws (sint.nat idx) = kb := by
                rw [← wMatch_key _ _ Hm]; exact (of_decide_eq_true hex).2
              have hh := pathKey_at r.ws (sint.nat idx) w kb kbs f hw' hkw HP
              first | exact Heq hh.2.symm | (rw [hh.1] at hb; exact hb Hf)
            have hE : ∀ w ∈ [(⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)], keyIn (bnd l).1 (bnd l).2 w.key ∧ ¬ isBktFlag w.flags := by
              intro w hw
              simp only [List.mem_singleton] at hw
              subst hw
              exact ⟨Hkin, fun hb => hb (by show (W32 0 &&& W32 1 : w32) = W32 0; decide)⟩
            have e1 : r'.nv.isLeaf' = true := by rw [Hr']; exact Hleaf
            ihave Htk := bktToks_leafOp γ W (uint.nat T.mv.pgid') bl B' Hc' l r r' Hr Hleaf e1
              (by rw [Hr']) A D C _ hws hws' (fun w hw => (hE w hw).2) $$ Htk
            ihave Hsh := txShape_close γ W T (wtxUpd T st' bl { B' with ns := <[l := r']> B'.ns }) bl B
              { B' with ns := <[l := r']> B'.ns } HB rfl Hg'.2.1 Hg'.1 Hrn
              (fun k v h => entryIn_leafOp W B' l r r' Hr Hleaf e1 A D C _ hws hws' hD k v (Hent k v h))
              ⟨bnd, bktKeysB_leafOp W _ bl B' Hc' bnd Hbkb l r r' Hr Hleaf A D C _ hws hws' hE e1
                (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr'])
                (fun _ => by rw [hws']; simp; omega)⟩ $$ [Hfr Htk]
            · iframe
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
            ihave Hbk : bktOwn (GF := GF) W bl { B' with ns := <[l := r']> B'.ns } $$ [Hbv Hib Hnm Hbm Hpo Hns]
            · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W { B' with ns := <[l := r']> B'.ns } B' rfl rfl rfl); iexact Hpo
            ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
            · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
            obtain ⟨Hle, Hlt, Hge⟩ := Hidx.2
            rw [← Hwl] at Hle
            have Hhex : ∀ w ∈ r'.ws, w = (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) ∨ w ∈ r.ws := fun w hw => by
              rw [Hr'] at hw; exact mem_putList _ _ _ _ _ hw
            ihave Hown := Hclose $$ %st' %({ B' with ns := <[l := r']> B'.ns }) [] Hrest Hmv Hpm Hbk Hv Hrh
            · ipureintro; exact ⟨bktClean_leafSet W _ bl B' Hc' l r r' Hr Hleaf (by rw [Hr']; exact Hleaf) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']; simp only [length_putList, h2]) (by rw [Hr']; simp only; rw [Hexeq]; exact wsSorted_putList r.ws (sint.nat idx) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) h3 Hle (fun k hk => by rw [← wMatch_key _ _ Hm]; exact Hlt k hk) (fun h => by rw [← wMatch_key _ _ Hm]; exact Hge (by rw [← Hwl]; exact h))) (fun w hw => by rcases Hhex w hw with rfl | hw; exact Hkpos; exact h4 w hw) (fun w hw => by rcases Hhex w hw with rfl | hw; exact ⟨by nofun, by nofun⟩; exact h5 w hw) (fun w hw hb => by rcases Hhex w hw with rfl | hw; exact (hb (by show (W32 0 &&& W32 1 : w32) = W32 0; decide)).elim; exact h11 Hleaf w hw hb), Htx', Hg'.1⟩
            iapply HΦ
            iframe
            isplitr
            · ipureintro; exact wtxSame_upd T _ bl B _ HB
            ileft; ipureintro; rfl
          · rw [Htx]
            icases txShape_open γ W T bl B HB $$ Hsh with ⟨Hbsh, Hfr, -⟩
            wp_apply hNode γ cl cv' path W (uint.nat T.mv.pgid') bl B txl _ T.t.pages' T.pm (DFrac.own 1)
              Hsk1 HwOK Hsk2 $$ [Hcl Hs Hctx Hstats Hbsh] as %l %B' %st' ⟨Hcl, Hs, Hctx, Hstats, Hbsh, %Hn⟩
            · iframe
            obtain ⟨Hc', Hg', ⟨r, Hr, Hleaf⟩, Hent, Hroute, Hpath⟩ := Hn
            obtain ⟨bnd, Hbkb, Hkin⟩ := Hroute kb Hkr
            have HP := Hpath kb _ Hpk r Hr
            have Hrn : B'.bv.rootNode' = null → B.bv.rootNode' = null := fun h => by
              rw [(Hc'.2.2.1 h).1] at Hr; cases Hr
            isimp only [bktShape] at Hbsh
            icases Hbsh with ⟨Htk, -⟩
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
              nk kb (DFrac.own halfQ) nk kb (DFrac.own halfQ) value vb dv (W64 0) (W32 0)
              ((wMatch_sorted _ _ Hm).2 h3) (by simp only [uint.nat] at H2; word) Hkpos Hkpos
              $$ [Hn Hins Hicap Hes Hbv1 Htxp Hmv Hnk1 Hnk2 Hval]
              as %idx %s' ⟨%Hidx, Hbv1, Htxp, Hmv, Hnk1, Hn, Hs', Hscap, Hes, Hold⟩
            · rw [h1, Htx']; iframe
            try wp_auto
            have Hexeq : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) =
                decide (sint.nat idx < r.ws.length ∧ wKey r.ws (sint.nat idx) = kb) := by
              rw [← Hwl, wMatch_key _ _ Hm]
            ihave Hes := inodesOwn_unput r.ins es (sint.nat idx) _ (internal.common.Inode.mk (W32 0) (W64 0) nk value)
              (NodeEntry.mk (W32 0) (W64 0) kb vb (DFrac.own halfQ) dv) Hil $$ [Hes Hold]
            · iframe
            icases Hes with ⟨Hes, Hx⟩
            ihave Hes := Hpback $$ Hes
            icases Hes with ⟨Hpv, Hents⟩
            ihave Hwx : wOwn (GF := GF) W (internal.common.Inode.mk (W32 0) (W64 0) nk value) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) $$ [Hx]
            · isimp only [inodeIs] at Hx
              icases Hx with ⟨-, Hxk, Hxv⟩
              unfold wOwn srcOwn; iframe; ipureintro; exact ⟨rfl, rfl⟩
            have Hhi : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) = true →
                sint.nat idx < r.ins.length := fun h => by rw [Hil]; exact (of_decide_eq_true h).1
            ihave Hents := bigSepL2_putList (fun it w => wOwn (GF := GF) W it w) r.ins r.ws (sint.nat idx) _
              (internal.common.Inode.mk (W32 0) (W64 0) nk value) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) h2 Hhi $$ [Hents Hwx]
            · iframe
            obtain ⟨r', Hr'⟩ : ∃ r' : NRec, r' = { r with nv := { r.nv with inodes' := s' }, ins := putList r.ins (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (internal.common.Inode.mk (W32 0) (W64 0) nk value), ws := putList r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) } := ⟨_, rfl⟩
            ihave Hnd : nodeOwn (GF := GF) W l r' $$ [Hn Hs' Hscap Hents Hch2 Hchcap Hkey]
            · rw [Hr']; unfold nodeOwn; iframe
            ihave Hns := Hnsback $$ %r' Hnd
            obtain ⟨A, D, C, hws, hws0, hD0⟩ := putList_split r.ws (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb)) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)
              (fun h => by rw [Hwl]; exact (of_decide_eq_true h).1)
            have hws' : r'.ws = A ++ [(⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)] ++ C := by rw [Hr']; exact hws0
            have hD : ∀ w ∈ D, ¬ isBktFlag w.flags := by
              intro w hw hb
              obtain ⟨hex, hw'⟩ := hD0 w hw
              have hkw : wKey r.ws (sint.nat idx) = kb := by
                rw [← wMatch_key _ _ Hm]; exact (of_decide_eq_true hex).2
              have hh := pathKey_at r.ws (sint.nat idx) w kb kbs f hw' hkw HP
              first | exact Heq hh.2.symm | (rw [hh.1] at hb; exact hb Hf)
            have hE : ∀ w ∈ [(⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry)], keyIn (bnd l).1 (bnd l).2 w.key ∧ ¬ isBktFlag w.flags := by
              intro w hw
              simp only [List.mem_singleton] at hw
              subst hw
              exact ⟨Hkin, fun hb => hb (by show (W32 0 &&& W32 1 : w32) = W32 0; decide)⟩
            have e1 : r'.nv.isLeaf' = true := by rw [Hr']; exact Hleaf
            ihave Htk := bktToks_leafOp γ W (uint.nat T.mv.pgid') bl B' Hc' l r r' Hr Hleaf e1
              (by rw [Hr']) A D C _ hws hws' (fun w hw => (hE w hw).2) $$ Htk
            ihave Hsh := txShape_close γ W T (wtxUpd T st' bl { B' with ns := <[l := r']> B'.ns }) bl B
              { B' with ns := <[l := r']> B'.ns } HB rfl Hg'.2.1 Hg'.1 Hrn
              (fun k v h => entryIn_leafOp W B' l r r' Hr Hleaf e1 A D C _ hws hws' hD k v (Hent k v h))
              ⟨bnd, bktKeysB_leafOp W _ bl B' Hc' bnd Hbkb l r r' Hr Hleaf A D C _ hws hws' hE e1
                (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr'])
                (fun _ => by rw [hws']; simp; omega)⟩ $$ [Hfr Htk]
            · iframe
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
            ihave Hbk : bktOwn (GF := GF) W bl { B' with ns := <[l := r']> B'.ns } $$ [Hbv Hib Hnm Hbm Hpo Hns]
            · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W { B' with ns := <[l := r']> B'.ns } B' rfl rfl rfl); iexact Hpo
            ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
            · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
            obtain ⟨Hle, Hlt, Hge⟩ := Hidx.2
            rw [← Hwl] at Hle
            have Hhex : ∀ w ∈ r'.ws, w = (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) ∨ w ∈ r.ws := fun w hw => by
              rw [Hr'] at hw; exact mem_putList _ _ _ _ _ hw
            ihave Hown := Hclose $$ %st' %({ B' with ns := <[l := r']> B'.ns }) [] Hrest Hmv Hpm Hbk Hv Hrh
            · ipureintro; exact ⟨bktClean_leafSet W _ bl B' Hc' l r r' Hr Hleaf (by rw [Hr']; exact Hleaf) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']; simp only [length_putList, h2]) (by rw [Hr']; simp only; rw [Hexeq]; exact wsSorted_putList r.ws (sint.nat idx) (⟨W32 0, W64 0, kb, vb, Src.own (DFrac.own halfQ), Src.own dv⟩ : WEntry) h3 Hle (fun k hk => by rw [← wMatch_key _ _ Hm]; exact Hlt k hk) (fun h => by rw [← wMatch_key _ _ Hm]; exact Hge (by rw [← Hwl]; exact h))) (fun w hw => by rcases Hhex w hw with rfl | hw; exact Hkpos; exact h4 w hw) (fun w hw => by rcases Hhex w hw with rfl | hw; exact ⟨by nofun, by nofun⟩; exact h5 w hw) (fun w hw hb => by rcases Hhex w hw with rfl | hw; exact (hb (by show (W32 0 &&& W32 1 : w32) = W32 0; decide)).elim; exact h11 Hleaf w hw hb), Htx', Hg'.1⟩
            iapply HΦ
            iframe
            isplitr
            · ipureintro; exact wtxSame_upd T _ bl B _ HB
            ileft; ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
