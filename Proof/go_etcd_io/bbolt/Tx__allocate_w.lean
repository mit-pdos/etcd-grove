module
public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Proof.go_etcd_io.bbolt.WriteAlloc
public import Proof.go_etcd_io.bbolt.DBAcc
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.Bucket__dereference
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.TxStats__IncPageCount
public import Spec.go_etcd_io.bbolt.TxStats__IncPageAlloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]
variable [linux : GOOSLinux]

theorem Tx.allocate.wp_wproof
    (hLog : DB.Logger.spec (GF := GF) (hG := hG))
    (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hAlloc : DB.allocate.spec (GF := GF) (hG := hG))
    (hDeref : Bucket.dereference.spec (GF := GF) (hG := hG))
    (hErrf : DefaultLogger.Errorf.spec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hPC : TxStats.IncPageCount.spec (GF := GF) (hG := hG))
    (hPA : TxStats.IncPageAlloc.spec (GF := GF) (hG := hG)) :
    Tx.allocate.wspec (GF := GF) (hG := hG) := by
  intro I γ W txl T σ count Hc0 Hc1 Hc2 Hpg Hhwm Hready Hdb Hcar Htxs Hps16
  wp_start as ⟨HR, HG, Hv⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  isimp only [dbWR] at HR
  icases HR with ⟨Hown, %Hf⟩
  obtain ⟨HAS, Hrw, Hdata, Hps, Hfli, w, Hw, Hwp, Hwq, Hwh⟩ := Hf
  icases ownDB_logger I W.dbl γ σ $$ Hown with ⟨%lg, %dl, #Hlg2, #Hdl2, #Hdlok, %Hlgf, Hown⟩
  unfold ownWriteTxG
  icases HG with ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩
  isimp only [TxW_rest_root] at Hrest
  icases Hrest with ⟨Hwritable, Hmanaged, Hdbf, Hmetaf, Hpages, Hstats, Hch, Hwf, %Htxn⟩
  isimp only [wView] at Hv
  icases Hv with ⟨Hdatav, #Hps', #Hlg, Hfliv, #Hdl, %Hlgv, Hpv⟩
  icombine Hdl Hdl2 gives %Hdle
  subst Hdle
  rw [Hdb]
  wp_auto
  wp_apply hLog W.dbl DFrac.discard W.lg W.dl Hlgf.2 $$ [Hlg Hdl] as Hlg'
  · iframe #
  have Hd : (if W.lg = interface.nil then discardIface W.dl else W.lg) = discardIface W.dl := by
    rcases Hlgv with h | h <;> rw [h] <;> simp [discardIface, interface.mkOk]
  rw [Hd]
  try wp_auto
  wp_apply hTxid T.t.meta' T.mv (DFrac.own 1) $$ [Hm] as Hm
  · iframe
  try wp_auto
  have Hderef' : σ.rwtx ≠ null →
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
          iprop(([∗map] bl ↦ B ∈ T.bs, bktOwn (GF := GF) W bl B) ∗
            structFieldRef Tx go!"stats" txl ↦ T.t.stats') ∗
          pagesView σ.data σ.ps w.q w.pages }}
        (App (Val (structFieldRef Tx go!"root" σ.rwtx @!! go.GoType.PointerType Bucket.ty @!!
          go!"dereference")) (Val #()))
      {{ RET #(); iprop(∃ T0, ⌜derefRel T T0⌝ ∗ ([∗map] bl ↦ B ∈ T0.bs, bktOwn (GF := GF) W bl B) ∗
            structFieldRef Tx go!"stats" txl ↦ T0.t.stats') ∗ pagesView σ.data σ.ps w.q w.pages }} := by
    intro _
    rw [Hrw, Hdata, Hps, Hwq, Hwp]
    iintro %Φ ⟨#Hpkg, ⟨Hbs, Hst⟩, Hpv⟩ HΦ
    wp_apply hDeref W txl T Hready Hcar Htxs $$ [Hbs Hst Hpv] as ⟨%T0, %Hrel, Hbs, Hst, Hpv⟩
    · iframe
    iapply HΦ
    iframe
    try (ipureintro; exact Hrel)
  wp_apply hAlloc I W.dbl γ σ w T.t.meta' T.mv
      (iprop(([∗map] bl ↦ B ∈ T.bs, bktOwn (GF := GF) W bl B) ∗
        structFieldRef Tx go!"stats" txl ↦ T.t.stats'))
      (iprop(∃ T0, ⌜derefRel T T0⌝ ∗ ([∗map] bl ↦ B ∈ T0.bs, bktOwn (GF := GF) W bl B) ∗
        structFieldRef Tx go!"stats" txl ↦ T0.t.stats'))
      T.mv.txid' count HAS Hw Hc0 Hc1 (by rw [Hps]; exact Hc2) (by rw [Hps]; exact Hpg)
      (by rw [Hwh]; exact Hhwm) Hderef'
      $$ [Hown Hdatav Hpv Hfliv Hmetaf Hm Hbs Hstats] as %p %err Hpost
  · rw [Hwq, Hdata, Hps, Hwp, Hrw, ← Hfli]
    iframe
  try wp_auto
  icases Hpost with (⟨%Herr, Hown, Hdatav, Hpv, Hfliv, Hmetaf, Hm, Hbs, Hstats⟩ | ⟨%Herr, Hmetaf, Hm, Hwr⟩ |
    ⟨%Herr, %σ', %mv', %id, %Hok, Hown, Hdatav, Hpv, Hfliv, Hmetaf, Hm, Hwr, Hpg⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok e => exact ⟨e, rfl⟩
    try rw [Hrw]
    try wp_auto
    wp_apply hTxid T.t.meta' T.mv (DFrac.own 1) $$ [Hm] as Hm
    · iframe
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply hErrf W.dl _ _ $$ [Hdlok]
    · iframe #
    try wp_auto
    iapply HΦ
    ileft
    iexists σ, W.data, T, T
    rw [show ({ W with data := W.data } : WView) = W from rfl]
    isplitl [Hown]
    · unfold dbWR; iframe; ipureintro; exact ⟨HAS, Hrw, Hdata, Hps, Hfli, w, Hw, Hwp, Hwq, Hwh⟩
    isplitl [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf Hm Hpm Hbufs Hbs]
    · unfold TxW_rest_root; rw [Hdb]; iframe; ipureintro; exact Htxn
    isplitl [Hdatav Hpv Hfliv]
    · unfold wView; rw [Hwq, Hdata, Hps, Hwp, Hfli]; iframe; iframe #; ipureintro; exact Hlgv
    ipureintro
    exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨by nofun, rfl⟩⟩
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok e => exact ⟨e, rfl⟩
    try rw [Hrw]
    try wp_auto
    wp_apply hTxid T.t.meta' T.mv (DFrac.own 1) $$ [Hm] as Hm
    · iframe
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply hErrf W.dl _ _ $$ [Hdlok]
    · iframe #
    try wp_auto
    iapply HΦ
    iright
    ipureintro; nofun
  · subst Herr
    obtain ⟨Hk1, Hk2, Hk3⟩ := allocOK_keeps σ σ' w T.mv mv' T.mv.txid' id (uint.nat count) Hok
    obtain ⟨Hid2, Hslots, Hmv', Hle, Hhw48, Hidn, -⟩ := Hok
    have Hcnt : 0 < uint.nat count := by have := Hc0; unfold uint.nat; word
    have Hc32 : uint.nat count ≤ 2 ^ 32 := by have := Hc1; unfold uint.nat; word
    have Hps80 : 16 ≤ σ.ps := by rw [Hps]; exact Hps16
    have H16 : 16 ≤ uint.nat count * σ.ps := Nat.le_trans Hps80 (Nat.le_mul_of_pos_left _ Hcnt)
    have Hpne : freshPage id (uint.nat count) σ.ps ≠ [] := by
      intro h; have := congrArg List.length h; simp [freshPage, leBytes_length'] at this
    ihave %Hpcar := bytesPointsto_car p _ _ Hpne $$ Hpg
    icases fresh_page_split p id (uint.nat count) σ.ps Hpcar Hcnt Hc32 H16 $$ Hpg with ⟨Hhd, Hpgback⟩
    try wp_auto
    wp_apply hId p _ (DFrac.own 1) $$ [Hhd] as Hhd
    · iframe
    ihave Hpg := Hpgback $$ Hhd
    try wp_auto
    wp_apply wp_mapInsert $$ [Hpm] as Hpm
    · iframe
    try wp_auto
    icases Hwr with (⟨%Hsd, Hbs, Hstats⟩ | ⟨%T0, %Hrel, Hbs, Hstats⟩)
    · wp_apply hPC _ _ count $$ [Hstats] as %st1 ⟨%Hst1, Hstats⟩
      · iframe
      try wp_auto
      wp_apply hPA _ _ _ $$ [Hstats] as %st2 ⟨%Hst2, Hstats⟩
      · iframe
      try wp_auto
      iapply HΦ
      ileft
      iexists σ', σ'.data, T, (allocT T st2 mv'.pgid' id p (freshPage id (uint.nat count) W.ps))
      isplitl [Hown]
      · unfold dbWR; iframe; ipureintro
        exact ⟨HAS, Hk1.trans Hrw, rfl, Hk3.trans Hps, Hfli, w, Hk2.trans Hw, Hwp, Hwq, Hwh⟩
      have HWd : ({ W with data := σ'.data } : WView) = W := by rw [Hsd, Hdata]
      rw [HWd]
      isplitl [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf Hm Hpm Hbufs Hpg Hbs]
      · unfold allocT TxW_rest_root
        rw [show ({ T.mv with pgid' := mv'.pgid' } : Meta) = mv' from Hmv'.symm]
        simp only
        rw [Hdb, Hrw]
        rw [← Hps]
        ihave Hbufs := bufs_insert T.pm T.bufs id p _ $$ [Hbufs Hpg]
        · iframe
        iframe
        ipureintro; exact Htxn
      isplitl [Hdatav Hpv Hfliv]
      · unfold wView; try simp only
        rw [Hwq, Hps, Hwp, Hfli]
        try rw [Hsd, Hdata]
        iframe; iframe #; ipureintro; exact Hlgv
      ipureintro
      refine ⟨Or.inl ⟨rfl, by rw [Hsd, Hdata]⟩, Or.inr ⟨rfl, id, st2, mv'.pgid', ?_, ?_, ?_, ?_, ?_, rfl⟩⟩
      · unfold uint.nat; word
      · unfold uint.nat; word
      · unfold uint.nat at Hidn ⊢; word
      · rw [← Hps]; exact Hhw48
      · rw [← Hwp]; exact Hslots
    · wp_apply hPC _ _ count $$ [Hstats] as %st1 ⟨%Hst1, Hstats⟩
      · iframe
      try wp_auto
      wp_apply hPA _ _ _ $$ [Hstats] as %st2 ⟨%Hst2, Hstats⟩
      · iframe
      try wp_auto
      iapply HΦ
      ileft
      iexists σ', σ'.data, T0, (allocT T0 st2 mv'.pgid' id p (freshPage id (uint.nat count) W.ps))
      isplitl [Hown]
      · unfold dbWR; iframe; ipureintro
        exact ⟨HAS, Hk1.trans Hrw, rfl, Hk3.trans Hps, Hfli, w, Hk2.trans Hw, Hwp, Hwq, Hwh⟩
      have Hrel2 := Hrel
      obtain ⟨Hrt, Hrmv, Hrpm, Hrbufs, -, -⟩ := Hrel2
      ihave Hbs := bs_reattach W { W with data := σ'.data } T0.bs (noView_of_derefRel T T0 Hrel) $$ Hbs
      isplitl [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf Hm Hpm Hbufs Hpg Hbs]
      · unfold allocT TxW_rest_root
        rw [Hrmv, show ({ T.mv with pgid' := mv'.pgid' } : Meta) = mv' from Hmv'.symm]
        simp only
        rw [Hrt, Hrpm, Hrbufs]
        simp only
        rw [Hdb, Hrw]
        rw [← Hps]
        ihave Hbufs := bufs_insert T.pm T.bufs id p _ $$ [Hbufs Hpg]
        · iframe
        iframe
        ipureintro; exact Htxn
      isplitl [Hdatav Hpv Hfliv]
      · unfold wView; try simp only
        rw [Hwq, Hps, Hwp, Hfli]
        try rw [Hsd, Hdata]
        iframe; iframe #; ipureintro; exact Hlgv
      ipureintro
      refine ⟨Or.inr ⟨Hrel, noView_of_derefRel T T0 Hrel⟩, Or.inr ⟨rfl, id, st2, mv'.pgid', ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · unfold uint.nat; word
      · rw [Hrmv]; unfold uint.nat; word
      · unfold uint.nat at Hidn ⊢; word
      · rw [← Hps]; exact Hhw48
      · rw [← Hwp]; exact Hslots
      · rfl

end proof

end bbolt
end EtcdGrove
end Perennial
