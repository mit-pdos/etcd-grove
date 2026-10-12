module
public import Spec.go_etcd_io.bbolt.Bucket__Delete
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.Bucket__Writable_w
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_w
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__node
public import Spec.go_etcd_io.bbolt.node__del

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

theorem Bucket.Delete.wp_proof (hLog : DB.Logger.spec (GF := GF) (hG := hG))
    (hWr : Bucket.Writable.wspec (GF := GF) (hG := hG))
    (hCur : Bucket.Cursor.wspec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek.wspec (GF := GF) (hG := hG))
    (hNode : Cursor.node.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG)) :
    Bucket.Delete.spec (GF := GF) (hG := hG) := by
  intro W txl T bl key kb dk Hbl
  obtain ⟨B, HB⟩ := Option.isSome_iff_exists.1 Hbl
  wp_start as ⟨Hown, Hk⟩
  icases ownWriteTx_bkt_acc W txl T bl B HB $$ Hown with ⟨%Hok, Hrest, Hmv, Hpm, Hb, Hv, Hclose⟩
  obtain ⟨HvOK, Hwr, Hdb, Hdbn, Hpm0, H2, Hhwm, Hroot, Hbs⟩ := Hok
  obtain ⟨Htx, Hclean, -⟩ := Hbs bl B HB
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  ihave #Hby : (isPkgInit (PROP := IProp GF) pkg_id.bytes) $$ []
  · iPkgInit
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
  wp_apply hWr bl B.bv (DFrac.own 1) T.t.writable' (DFrac.own 1) $$ [Hbv Hwritable] as ⟨Hbv, Hwritable⟩
  · rw [Htx]; iframe
  rw [Hwr]
  try wp_auto
  rw [Htx]
  wp_apply hCur bl B.bv (DFrac.own 1) T.t.stats' $$ [Hbv Hstats] as %cl %s ⟨Hcl, Hs, Hcap, Hbv, Hstats⟩
  · rw [Htx]; iframe
  try wp_auto
  have HwOK : wctxOK W (uint.nat T.mv.pgid') bl B txl T.pm := ⟨HvOK, Hclean, Htx, fun id _ => by rw [Hpm0]; rfl⟩
  wp_apply hSeek cl { bucket' := bl, stack' := s } [] W (uint.nat T.mv.pgid') bl B txl T.t.pages' T.pm
    (DFrac.own 1) key kb dk rfl HwOK $$ [Hcl Hs Hcap Hbv Hib Hnm Hbm Hpo Hns Hdata Hpv Hfli Hpages Hpm Hdbf Hk]
    as %cv' %path %k %v %f ⟨%Hsk, Hcl, Hs, Hcap, Hctx, Hk⟩
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
  icases keySrc_acc W bl B txl T.t.pages' T.pm (DFrac.own 1) k HvOK.1 Hsk.2.2 $$ Hctx
    with ⟨%dq, %bs, Hkk, Hkback⟩
  wp_apply bytes.wp_Equal key k dk dq kb bs $$ [Hk Hkk] as ⟨Hk, Hkk⟩
  · iframe
  ihave Hctx := Hkback $$ Hkk
  try wp_auto
  by_cases Heq : kb = bs
  · rw [decide_eq_true Heq]
    try wp_auto
    by_cases Hf : f &&& W32 1 = W32 0
    · rw [decide_eq_true Hf]
      try wp_auto
      rw [Htx]
      wp_apply hNode cl cv' path W (uint.nat T.mv.pgid') bl B txl _ T.t.pages' T.pm (DFrac.own 1)
        Hsk.1 HwOK Hsk.2.1 $$ [Hcl Hs Hctx Hstats] as %l %B' %st' ⟨Hcl, Hs, Hctx, Hstats, %Hn⟩
      · iframe
      obtain ⟨Hc', Hg', r, Hr, Hleaf⟩ := Hn
      obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, h11, -⟩ := Hc'.2.2.2.2.2.2.2.1 l r Hr
      have Htx' : B'.bv.tx' = txl := (bktGrows_tx B B' Hg').trans Htx
      isimp only [wctx] at Hctx
      icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
      icases bktOwn_node_acc W bl B' l r Hr $$ Hbk with ⟨Hnd, Hback⟩
      isimp only [nodeOwn] at Hnd
      icases Hnd with ⟨Hn, Hins, Hicap, Hents, Hch2, Hchcap, Hkey⟩
      isimp only [wView] at Hv
      icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
      icases nodeBorrow W HvOK.1 r.ws r.ins W.q h5 $$ [Hpv Hents] with ⟨%es, %Hm, Hes, Hpback⟩
      · iframe
      try wp_auto
      wp_apply hDel l r.nv r.ins es key kb dk ((wMatch_sorted _ _ Hm).2 h3) $$ [Hn Hins Hicap Hes Hk]
        as %idx ⟨%Hidx, Hk, Hres⟩
      · iframe
      try wp_auto
      have Hwl := wMatch_length Hm
      by_cases Hex : sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb
      · isimp only [decide_eq_true Hex, ↓reduceIte] at Hres
        icases Hres with ⟨%it, %e, %Hie, Hie, Hn, Hins, Hicap, Hes⟩
        ihave Hes := inodesOwn_undel r.ins es (sint.nat idx) it e Hie.1 Hie.2 $$ [Hes Hie]
        · iframe
        ihave Hes := Hpback $$ Hes
        icases Hes with ⟨Hpv, Hents⟩
        ihave Hents := bigSepL2_eraseIdx (fun it w => wOwn (GF := GF) W it w) r.ins r.ws (sint.nat idx)
          h2 (by omega) $$ Hents
        obtain ⟨r', Hr'⟩ : ∃ r' : NRec, r' = { r with nv := { r.nv with inodes' := slice.slice r.nv.inodes' internal.common.Inode (W64 0) (r.nv.inodes'.len - W64 1), unbalanced' := true }, ins := r.ins.eraseIdx (sint.nat idx), ws := r.ws.eraseIdx (sint.nat idx) } := ⟨_, rfl⟩
        ihave Hbk := Hback $$ %r' [Hn Hins Hicap Hents Hch2 Hchcap Hkey]
        · rw [Hr']; unfold nodeOwn; iframe
        ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
        · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
        ihave Hown := Hclose $$ %(st') %({ B' with ns := <[l := r']> B'.ns }) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
        · ipureintro; exact ⟨bktClean_leafSet W _ bl B' Hc' l r r' Hr Hleaf (by rw [Hr']; exact Hleaf) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']) (by rw [Hr']; simp [List.length_eraseIdx, h2]) (by rw [Hr']; exact wsSorted_eraseIdx _ _ h3) (by rw [Hr']; exact fun w hw => h4 w (List.mem_of_mem_eraseIdx hw)) (by rw [Hr']; exact fun w hw => h5 w (List.mem_of_mem_eraseIdx hw)) (by rw [Hr']; exact fun w hw => h11 Hleaf w (List.mem_of_mem_eraseIdx hw)), Htx', Hg'.1⟩
        · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
        iapply HΦ
        iframe
        ipureintro; exact wtxSame_upd T _ bl B _ HB
      · isimp only [decide_eq_false Hex, Bool.false_eq_true, ↓reduceIte] at Hres
        icases Hres with ⟨Hn, Hins, Hicap, Hes⟩
        ihave Hes := Hpback $$ Hes
        icases Hes with ⟨Hpv, Hents⟩
        ihave Hbk := Hback $$ %r [Hn Hins Hicap Hents Hch2 Hchcap Hkey]
        · unfold nodeOwn; iframe
        rw [bktOwn_insert_same W bl B' l r Hr]
        ihave Hv : wView (GF := GF) W $$ [Hdata Hpv Hfli]
        · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
        ihave Hown := Hclose $$ %(st') %(B') [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
        · ipureintro; exact ⟨Hc', Htx', Hg'.1⟩
        · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
        iapply HΦ
        iframe
        ipureintro; exact wtxSame_upd T _ bl B _ HB
    · rw [decide_eq_false Hf]
      try wp_auto
      icases bboltError_access errors.ErrIncompatibleValue (by simp [bboltErrorNames]) $$ Hei
        with ⟨%e, #He, %Hne⟩
      try wp_auto
      rw [Htx]
      isimp only [wctx] at Hctx
      icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
      ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
      · ipureintro; exact ⟨Hclean, Htx, rfl⟩
      · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
      iapply HΦ
      iframe
      ipureintro; exact wtxSame_upd T _ bl B _ HB
  · rw [decide_eq_false Heq]
    try wp_auto
    rw [Htx]
    isimp only [wctx] at Hctx
    icases Hctx with ⟨Hbk, Hv, Hpages, Hpm, Hdbf⟩
    ihave Hown := Hclose $$ %({ T.t.stats' with CursorCount' := T.t.stats'.CursorCount' + W64 1 }) %(B) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
    · ipureintro; exact ⟨Hclean, Htx, rfl⟩
    · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
    iapply HΦ
    iframe
    ipureintro; exact wtxSame_upd T _ bl B _ HB

end proof

end bbolt
end EtcdGrove
end Perennial
