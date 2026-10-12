module
public import Spec.go_etcd_io.bbolt.Bucket__NextSequence_s
public import Spec.go_etcd_io.bbolt.Bucket__Writable_w
public import Spec.go_etcd_io.bbolt.Bucket__node_s
public import Proof.go_etcd_io.bbolt.ShapeOpen
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__IncSequence
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__InSequence

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

theorem Bucket.NextSequence.wp_sproof (hWr : Bucket.Writable.wspec (GF := GF) (hG := hG))
    (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hnode : Bucket.node.sspec (GF := GF) (hG := hG))
    (hInc : InBucket.IncSequence.spec (GF := GF) (hG := hG))
    (hInS : InBucket.InSequence.spec (GF := GF) (hG := hG)) :
    Bucket.NextSequence.sspec (GF := GF) (hG := hG) := by
  intro γ W txl T bl Hbl
  obtain ⟨B, HB⟩ := Option.isSome_iff_exists.1 Hbl
  wp_start as ⟨Hown, Hsh⟩
  icases txShape_acc γ W T bl B HB $$ Hsh with ⟨Hbs, Hshback⟩
  icases ownWriteTx_bkt_acc W txl T bl B HB $$ Hown with ⟨%Hok, Hrest, Hmv, Hpm, Hb, Hv, Hclose⟩
  obtain ⟨HvOK, Hwr, Hdb, Hdbn, Hpm0, H2, Hhwm, Hroot, Hbs⟩ := Hok
  obtain ⟨Htx, Hclean, -⟩ := Hbs bl B HB
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  isimp only [TxW_rest_root] at Hrest
  icases Hrest with ⟨Hwritable, Hmanaged, Hdbf, Hmetaf, Hpages, Hstats, Hch, Hwf, %Htxn⟩
  isimp only [bktOwn] at Hb
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  try wp_auto
  rw [Htx, Hdb]
  try wp_auto
  rw [decide_eq_false Hdbn]
  try wp_auto
  wp_apply hWr bl B.bv (DFrac.own 1) T.t.writable' (DFrac.own 1) $$ [Hbv Hwritable] as ⟨Hbv, Hwritable⟩
  · rw [Htx]; iframe
  rw [Hwr]
  try wp_auto
  try rw [Htx]
  by_cases Hrn : B.bv.rootNode' = null
  · rw [decide_eq_true Hrn]
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply hRoot $$ [Hib] as Hib
    · iframe
    try wp_auto
    obtain ⟨p, pg, Hpa⟩ := rootPage_exists W _ bl B Hclean Hrn
    have Hres0 := resolve_root_none W _ bl B Hclean Hrn
    obtain ⟨Hlen, Hinl⟩ := rootPage_facts W _ bl B Hclean Hres0 p pg Hpa
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    icases wpageAt_acc (GF := GF) W B B.ib.root' p pg HvOK.1 Hpa Hinl
      (by intro h; rw [h] at Hlen; simp at Hlen) $$ [Hpv Hpo] with ⟨%dq, %Hcar, Hpg, Hpgback⟩
    · iframe
    ihave Hpvpo := Hpgback $$ Hpg
    icases Hpvpo with ⟨Hpv, Hpo⟩
    have Hsrc := rootSrcOK W _ bl B T.pm HvOK Hclean (fun id _ => by rw [Hpm0]; rfl) Hres0 p pg Hpa Hcar
    wp_apply hnode γ W (uint.nat T.mv.pgid') bl B txl T.t.stats' T.t.pages' T.pm (DFrac.own 1)
      B.ib.root' null p pg _ HvOK Hclean Htx (fun _ => ⟨Hsrc, Or.inl ⟨rfl, Hrn, rfl⟩⟩)
      $$ [Hbv Hib Hnm Hbm Hpo Hns Hdata Hpv Hfli Hstats Hpages Hpm Hdbf Hbs]
      as %l %B1 %st1 ⟨Hbk, Hv, Hstats, Hpages, Hpm, Hdbf, Hbs, %Hres2⟩
    · isplitl [Hbv Hib Hnm Hbm Hpo Hns]
      · unfold bktOwn; iframe
      isplitl [Hdata Hpv Hfli]
      · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
      iframe
    have Hres := Hres2.1
    obtain ⟨Hc1, Hg1⟩ := rootStep0 W _ bl B HvOK Hclean Hrn p pg Hpa l B1 _ _ Hres
    have Hrn1 := nodeRes_root_ne W _ bl B Hclean Hrn p pg _ l B1 _ _ Hres
    isimp only [bktOwn] at Hbk
    icases Hbk with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply hInc $$ [Hib] as Hib
    · iframe
    try wp_auto
    wp_method_call
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply hInS $$ [Hib] as Hib
    · iframe
    try wp_auto
    ihave Hbk : bktOwn (GF := GF) W bl ({ B1 with ib := { (B1).ib with sequence' := (B1).ib.sequence' + 1 } }) $$ [Hbv Hib Hnm Hbm Hpo Hns]
    · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W ({ B1 with ib := { (B1).ib with sequence' := (B1).ib.sequence' + 1 } }) (B1) rfl rfl rfl); iexact Hpo
    ihave Hown := Hclose $$ %(st1) %({ B1 with ib := { (B1).ib with sequence' := (B1).ib.sequence' + 1 } }) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
    · ipureintro; exact ⟨bktClean_ib W _ bl (B1) _ rfl Hc1, ((bktGrows_tx B B1 Hg1).trans Htx), Hg1.1⟩
    · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
    isimp only [bktShape] at Hbs
    icases Hbs with ⟨Hbt, %Hbkk⟩
    ihave Hsh := Hshback $$ %(wtxUpd T st1 bl { B1 with ib := { (B1).ib with sequence' := (B1).ib.sequence' + 1 } }) %({ B1 with ib := { (B1).ib with sequence' := (B1).ib.sequence' + 1 } }) [] [Hbt]
    · ipureintro
      exact ⟨rfl, by show B1.ib.root' = B.ib.root'; rw [Hg1.2.1], fun h => absurd h Hrn1, Hg1.1,
        Hres2.2, Hbkk⟩
    · iapply (bktToks_ib γ W B1 { (B1).ib with sequence' := (B1).ib.sequence' + 1 } rfl).2; iexact Hbt
    iapply HΦ
    iframe
    ipureintro; exact wtxSame_upd T _ bl B _ HB
  · rw [decide_eq_false Hrn]
    try wp_auto
    ihave Hbk : bktOwn (GF := GF) W bl B $$ [Hbv Hib Hnm Hbm Hpo Hns]
    · unfold bktOwn; iframe
    isimp only [bktOwn] at Hbk
    icases Hbk with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply hInc $$ [Hib] as Hib
    · iframe
    try wp_auto
    wp_method_call
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply hInS $$ [Hib] as Hib
    · iframe
    try wp_auto
    ihave Hbk : bktOwn (GF := GF) W bl ({ B with ib := { (B).ib with sequence' := (B).ib.sequence' + 1 } }) $$ [Hbv Hib Hnm Hbm Hpo Hns]
    · unfold bktOwn; iframe; iapply (pageOwn_congr_wand W ({ B with ib := { (B).ib with sequence' := (B).ib.sequence' + 1 } }) (B) rfl rfl rfl); iexact Hpo
    ihave Hown := Hclose $$ %(T.t.stats') %({ B with ib := { (B).ib with sequence' := (B).ib.sequence' + 1 } }) [] [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf] Hmv Hpm Hbk Hv
    · ipureintro; exact ⟨bktClean_ib W _ bl (B) _ rfl Hclean, Htx, rfl⟩
    · unfold TxW_rest_root; simp only; rw [Hwr, Hdb]; iframe; ipureintro; exact Htxn
    isimp only [bktShape] at Hbs
    icases Hbs with ⟨Hbt, %Hbkk⟩
    ihave Hsh := Hshback $$ %(wtxUpd T T.t.stats' bl { B with ib := { (B).ib with sequence' := (B).ib.sequence' + 1 } }) %({ B with ib := { (B).ib with sequence' := (B).ib.sequence' + 1 } }) [] [Hbt]
    · ipureintro
      exact ⟨rfl, rfl, fun h => absurd h Hrn, rfl, fun _ _ h => h, Hbkk⟩
    · iapply (bktToks_ib γ W B { (B).ib with sequence' := (B).ib.sequence' + 1 } rfl).2; iexact Hbt
    iapply HΦ
    iframe
    ipureintro; exact wtxSame_upd T _ bl B _ HB

end proof

end bbolt
end EtcdGrove
end Perennial
