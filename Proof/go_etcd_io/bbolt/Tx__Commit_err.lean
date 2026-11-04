/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Commit_err.lean` (U10g of `notes/bbolt-proof-plan.md`;
design §3.11): the writer's `boltTx` opened as `Tx.Rollback.wp_writer` does (`boltTxDef_wtxW`,
`txExcl_take`, `txExclWGap_holds`); the logger and its deferred line; `rebalance`, `spill`, the
root's header, the old freelist page freed, `commitFreelist` (or `NoFreelistSync`), `grow`,
`write`, `writeMeta` (the commit point `commitStep_commit`), `close`. Every error path ends at
`Tx.rollback.spec`.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Commit_err
public import Proof.go_etcd_io.bbolt.Tx__Rollback
public import Proof.go_etcd_io.bbolt.Commit.AssembleLog
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Commit.Getters
public import Proof.go_etcd_io.bbolt.Commit.RollbackSpec
public import Proof.go_etcd_io.bbolt.Commit.Step
public import Proof.go_etcd_io.bbolt.Tx__write
public import Proof.go_etcd_io.bbolt.Tx__commitFreelist
public import Spec.go_etcd_io.bbolt.Bucket__rebalance
public import Spec.go_etcd_io.bbolt.Bucket__spill
public import Spec.go_etcd_io.bbolt.DB__grow
public import Spec.go_etcd_io.bbolt.DB__page
public import Spec.go_etcd_io.bbolt.TxStats__GetRebalance
public import Spec.go_etcd_io.bbolt.TxStats__IncRebalanceTime
public import Spec.go_etcd_io.bbolt.TxStats__IncSpillTime
public import Spec.go_etcd_io.bbolt.TxStats__IncWriteTime
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetFreelist
public import Spec.go_etcd_io.bbolt.internal.common.Meta__RootBucket
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__SetRootPage
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Free
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.bbolt.Commit.AssembleAcc
public import Proof.go_etcd_io.bbolt.Commit.AssemblePure
public import Proof.go_etcd_io.bbolt.Commit.AssembleEnd
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common
open _root_.Perennial.fmt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

private instance BC_full_persistent_cm (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

private instance viewOf_persistent_cm (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

omit hos package_sem in
/-- An `int` is an argument `fmt` formats with no method. -/
theorem logArgOk_int (R : IProp GF) (v : w8) (n : w64) :
    ⊢ logArgOk (GF := GF) R v (interface.mkOk go.int #n) := by
  unfold interface.mkOk
  apply logArgOk_of_argWf
  have hi : IsIntType go.int := by simp [IsIntType]
  refine ⟨fun h => absurd h (by simp [go.int, go.string]), fun _ => ⟨_, .int n⟩,
    Or.inr (Or.inl hi)⟩

/-- The tail of an error path after the rollback: return `err` (the deferred line runs on it). -/
syntax "cm_return" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| cm_return) => `(tactic| (
      try wp_auto
      wp_bind (App (Val #_) (Val #()))
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ _))) $$ [err HtxId Hlgp]
      · iapply Hdf $$ [] err HtxId Hlgp
        iright; iexact Hfe1
      iintro %vret ⟨%hvret, err⟩
      subst hvret
      wp_auto
      iapply HΦ
      unfold txDone
      iframe Hdone
      iright
      isplitr
      · ipureintro; exact fun h => by cases h
      iframe Hfe1
      iright
      iexact Hau))

omit package_sem in
private theorem cm_wdbW_ok (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ ⌜wdbOK w ∧ w.ms = some (v.base, mapLen w.ms) ∧ v = View.ofC v.base w.C⌝ := by
  unfold wdbW; iintro ⟨-, %h⟩; ipureintro; exact h

omit package_sem in
private theorem cm_wdbLost_ok (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbLost (GF := GF) K tx v w ⊢ ⌜wdbOK w ∧ w.ms = none⌝ := by
  unfold wdbLost; iintro ⟨-, %h⟩; ipureintro; exact h

omit hos sem package_sem in
private theorem cm_keep_pure {Q : IProp GF} {P : Prop} (h : Q ⊢ ⌜P⌝) : Q ⊢ Q ∗ ⌜P⌝ := by
  refine (BI.and_intro h .rfl).trans ?_
  refine persistent_and_affinely_sep_left_mp.trans ?_
  iintro ⟨%HP, HQ⟩
  iframe
  ipureintro; exact HP

theorem Tx.Commit_err.wp_proof'
    (wp_Assert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (wp_ID : Tx.ID.spec (GF := GF) (hG := hG))
    (wp_rebalance : Bucket.rebalance.spec (GF := GF) (hG := hG))
    (wp_spill : Bucket.spill.spec (GF := GF) (hG := hG))
    (wp_rollback : Tx.rollback.spec (GF := GF) (hG := hG))
    (wp_close : Tx.close_w.spec (GF := GF) (hG := hG))
    (wp_commitFreelist : Tx.commitFreelist.spec (GF := GF) (hG := hG))
    (wp_grow : DB.grow.spec (GF := GF) (hG := hG))
    (wp_write : Tx.write.spec (GF := GF) (hG := hG))
    (wp_writeMeta : Tx.writeMeta.spec (GF := GF) (hG := hG))
    (wp_page : DB.page.spec (GF := GF) (hG := hG))
    (wp_GetRebalance : TxStats.GetRebalance.spec (GF := GF) (hG := hG))
    (wp_IncRebalanceTime : TxStats.IncRebalanceTime.spec (GF := GF) (hG := hG))
    (wp_IncSpillTime : TxStats.IncSpillTime.spec (GF := GF) (hG := hG))
    (wp_IncWriteTime : TxStats.IncWriteTime.spec (GF := GF) (hG := hG))
    (wp_Pgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_Freelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (wp_SetFreelist : internal.common.Meta.SetFreelist.spec (GF := GF) (hG := hG))
    (wp_RootBucket : internal.common.Meta.RootBucket.spec (GF := GF) (hG := hG))
    (wp_RootPage : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (wp_SetRootPage : internal.common.InBucket.SetRootPage.spec (GF := GF) (hG := hG))
    (wp_FlFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG)) :
    Tx.Commit_err.spec (GF := GF) (hG := hG) := by
  intro tx γ T Q
  wp_start as ⟨Ht, %hrw, Hau⟩
  unfold boltTx
  icases (boltTxDef_wtxW _ _ tx T hrw).1 $$ Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hB, hN, hT⟩ := HK
  rw [← hB]
  iunfold wtxW at Hw
  icases Hw with ⟨Hcore, Hvc, Hmf⟩
  iunfold wtxCore at Hcore
  icases Hcore with ⟨#Hpkg, #Hkc, %Hc, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, #Hvo, Hstok⟩
  obtain ⟨hdb, hrwr, htxn, hmg, hrootn⟩ := Hc
  simp only [statsTok, ↓reduceIte]
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hkc
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, -, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  imod txExcl_take K.B K.N K.p K.sp K.t0 ⊤ CoPset.subseteq_top tx r $$ [Hti Hreg Hstok] with Hx
  · iframe; iframe #
  iunfold wtxHeap at Hh
  icases Hh with ⟨%Hhok, Hf, Hrf, Hobj, Hbobj⟩
  iunfold txFields at Hf
  icases Hf with ⟨Hwr, Hmg, Hme, Hpgs, Hch, Hwfl, Hmv, Hpm, Hbufs⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hmv with ⟨Hmv, %Hmvn⟩
  ihave #Hfix' := Hfix
  iunfold dbFixed at Hfix'
  icases Hfix' with ⟨-, -, ⟨%lg, #Hlg, #Hlgok⟩, -⟩
  ihave %Hlgty := dbFixed_logPtrTyped K.db K.sp lg $$ Hfix Hlg
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  rw [hmg, hdb]
  wp_auto
  ihave Hg := txExclWGap_holds K tx r X c hdb $$ [Hx Hv]
  · iframe
  icases Hg with ⟨Hv, Hd, Hrwl, Hcls, Hg⟩
  icases Hg with ⟨%w, %extra, Hwdb, -, %Hflv⟩
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply wp_ID tx X.t.t.meta' X.t.mv _ _ htxn Hmvn $$ [Hme Hmv] as ⟨Hme, Hmv⟩
  · iframe
  try wp_auto
  wp_apply DB.Logger.wp_proof K.db lg Ht0.2.1 $$ []
  · iframe #; unfold dbLogger; iexact Hlgok
  try wp_auto
  wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
  wp_apply cm_logger_ne_discard lg Hlgty $$ [] as %bl -
  · iframe #; unfold dbLogger; iexact Hlgok
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ txId_ptr ↦ X.t.mv.txid' ∗ lg_ptr ↦ lg ∗
      ∃ f : GoFunc, defer ↦ f ∗ □ (∀ e : GoInterface, (⌜e = interface.nil⌝ ∨ fmtErrorOk e) -∗
        err_ptr ↦ e -∗ txId_ptr ↦ X.t.mv.txid' -∗ lg_ptr ↦ lg -∗
        WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ err_ptr ↦ e }})))) $$ [txId lg defer]
  · cases bl
    · wp_auto
      iframe
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %e - Herr - -
      wp_auto
      iframe; try (ipureintro; rfl)
    · cases lg with
      | nil => iexfalso; unfold dbLogger boltLogger; iexact Hlgok
      | ok li =>
      ihave #Hlgok' : boltLogger (GF := GF) (.ok li) $$ []
      · unfold dbLogger; iexact Hlgok
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      try wp_auto
      wp_apply wp_boltLog li _ _ [W8 100] _ [interface.mkOk go.int #X.t.mv.txid'] _ iprop(True) _
        (by decide) (by decide) rfl $$ Hlgok' [Hsl] [] [] as Hsl -
      · iframe
      · try simp only [List.zip_cons_cons, List.zip_nil_left]
        isplitl
        · iapply logArgOk_int
        · iempintro
      try wp_auto
      isplitr
      · ipureintro; rfl
      iframe
      imodintro
      iintro %e Hen Herr Htx Hlg
      wp_auto
      icases Hen with (%he | #Hfe)
      · subst he
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 100] _ [interface.mkOk go.int #X.t.mv.txid'] _ iprop(True) _
          (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [] as Hsl2 -
        · iframe
        · try simp only [List.zip_cons_cons, List.zip_nil_left]
          isplitl
          · iapply logArgOk_int
          · iempintro
        try wp_auto
        iframe; try (ipureintro; rfl)
      · cases e with
        | nil =>
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          try wp_auto
          wp_apply wp_boltLog li _ _ [W8 100] _ [interface.mkOk go.int #X.t.mv.txid'] _ iprop(True) _
            (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [] as Hsl2 -
          · iframe
          · try simp only [List.zip_cons_cons, List.zip_nil_left]
            isplitl
            · iapply logArgOk_int
            · iempintro
          try wp_auto
          iframe; try (ipureintro; rfl)
        | ok ii =>
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          try wp_auto
          wp_apply wp_boltLog li _ _ [W8 118] _ [GoInterface.ok ii] _ iprop(True) _
            (by decide) (by decide) rfl $$ Hlgok' [Hsl2] [] [] as Hsl2 -
          · iframe
          · try simp only [List.zip_cons_cons, List.zip_nil_left]
            isplitl
            · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe
            · iempintro
          try wp_auto
          iframe; try (ipureintro; rfl)
  iintro %v ⟨%hv, HtxId, Hlgp, %f, Hdefer, #Hdf⟩
  subst hv
  have hwr : X.t.t.writable' = true := Hf.1.1.1
  wp_auto
  wp_apply wp_Assert
  rw [decide_eq_false Ht0.2.1]
  wp_auto
  rw [hwr]
  wp_auto
  wp_apply time.wp_Now as %t0 -
  try wp_auto
  -- `rebalance`: the working state in mode `false`
  ihave Hw : wtxW K tx r false X $$ [Hvc Hmf Hfills Hbk Hnl Hdb Hd Hrf Hobj Hbobj Hwr Hmg Hme Hpgs Hch
      Hwfl Hmv Hpm Hbufs]
  · unfold wtxW wtxCore statsTok wtxHeap txFields
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hdb, hmg, hwr]
    iframe
    iframe #
    ipureintro
    exact ⟨⟨rfl, hrwr, htxn, rfl, hrootn⟩, Hhok⟩
  have Hmeta : metaCopyOK X.t.mv w.C := Hflv.2.1
  icases (cm_keep_pure (cm_wdbW_ok K tx X.v w)) $$ Hwdb
    with ⟨Hwdb, %Hwok⟩
  have hbase : T.base = treeData w.C := by
    rw [Hf.2.2.1]
    have e : X.v.data = (View.ofC X.v.base w.C).data := congrArg View.data Hwok.2.2
    rw [e]; rfl
  ihave Hex : cmExcl K r X (treeData w.C) $$ [Hrwl Hcls Hv Hst]
  · unfold cmExcl; rw [← hbase]
    iframe
  have hvwf : viewWF X.v := Hf.1.2.2.2.2.2.2.2
  have hld : ∀ bl, X.t.bs !! bl ≠ none → leafDepthOK X bl := fun bl hb =>
    leafDepthOK_rt X bl (rtOK_init X bl Hf.1 hvwf (Option.isSome_iff_ne_none.2 hb))
  wp_apply wp_rebalance K tx r false X w Hf.1 hld Hf.2.2.2.2.1 Hflv.1 $$ [Hw Hwdb]
    as ⟨%X1, %fl1, Hw, Hwdb, %Hrb⟩
  · iframe
  imod cm_excl_update K r X X1 _ $$ Hex
    with Hex
  icases cm_stats_acc K tx r false X1 $$ Hw with ⟨-, -, Hst1, Hwb⟩
  wp_apply wp_GetRebalance K tx r false 1 $$ [Hst1] as %nrb Hst1
  · iframe; iframe #
  try wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ statsTok r false 1 ∗
    startTime_ptr ↦ t0 ∗ tx_ptr ↦ tx))) $$ [Hst1 startTime tx]
  · wp_if_destruct
    · try wp_auto
      wp_apply time.wp_Since as %d -
      try wp_auto
      wp_apply wp_IncRebalanceTime K tx r false 1 $$ [Hst1] as %_ Hst1
      · iframe; iframe #
      try wp_auto
      iframe
      try (ipureintro; rfl)
    · try wp_auto
      iframe
      try (ipureintro; rfl)
  iintro %v ⟨%hv, Hst1, startTime, tx⟩
  subst hv
  ihave Hw := Hwb $$ Hst1
  -- `opgid`
  icases cm_meta_acc K tx r false X1 $$ Hw with ⟨Hme, Hmv, Hwb⟩
  wp_auto
  wp_apply wp_Pgid $$ [Hmv] as Hmv
  · iframe #; iframe
  ihave Hw := Hwb $$ %X1.t.mv Hme Hmv
  have eX1 : X1.withMv X1.t.mv = X1 := rfl
  rw [eX1]
  try wp_auto
  wp_apply time.wp_Now as %t1 -
  try wp_auto
  -- `spill`
  obtain ⟨hrbOK, hreach1, hflv1, htt1, hmv1⟩ := Hrb
  have hv1 : X1.v = X.v := hrbOK.2.2.1
  rw [← hv1]
  have hmap1 : X1.t.mv.pgid'.toNat * 4096 ≤ mapLen (w.withFl fl1).ms := by
    rw [hmv1, show (w.withFl fl1).ms = w.ms from rfl, Hmeta.2.2.2.1]
    exact Hwok.1.2.2.2.2.2.2.2.2.1 _ _ Hwok.2.1
  -- the spill's start: the committed tree, the mark, the root bucket's children
  -- (local gap: `rebalance`'s post says nothing of the root bucket's `bm`; `wrFacts` and
  -- `gensOK_bktLoc_inj` give it of `X`)
  have hroot1 : ∀ B0, X1.t.bs !! X1.rl = some B0 → (∀ k c, B0.bm !! k = some c → c ≠ X1.rl) ∧
      ∀ k k' c, B0.bm !! k = some c → B0.bm !! k' = some c → k = k' := sorry
  have hstart1 : spillStartOK X1 (w.withFl fl1) :=
    ⟨Hflv.2.2, by rw [hmv1, Hmeta.2.2.2.1]; exact Nat.le_refl _, hroot1⟩
  wp_apply wp_spill K tx r false X1 (w.withFl fl1) (spillPre_of_rebalOK X X1 w.fl fl1 _ hrbOK)
    hreach1 hmap1 hflv1 hstart1 $$ [Hw Hwdb] as %err1 Hsp
  · iframe
  cases lg with
  | nil => iexfalso; unfold dbLogger boltLogger; iexact Hlgok
  | ok li =>
  ihave #Hlgok' : boltLogger (GF := GF) (.ok li) $$ []
  · unfold dbLogger; iexact Hlgok
  icases Hsp with (⟨%He1, %X2, %w2, Hw, Hwdb, %Hsp⟩ | ⟨%He1, #Hfe1, %X2, %w2, %st, %Hsp, Hres⟩)
  · -- spilled
    subst He1
    obtain ⟨hspOK, hC2, hderef2, hfresh2, hreach2, hmap2, hflv2, hbufs2, htt2, hrl2e, hrl2, hmv2⟩ := Hsp
    try wp_auto
    wp_apply time.wp_Since as %d -
    try wp_auto
    icases cm_stats_acc K tx r false X2 $$ Hw with ⟨-, -, Hst2, Hwb⟩
    wp_apply wp_IncSpillTime K tx r false 1 $$ [Hst2] as %_ Hst2
    · iframe; iframe #
    ihave Hw := Hwb $$ Hst2
    try wp_auto
    -- `tx.meta.RootBucket().SetRootPage(tx.root.RootPage())`
    icases cm_heapOK K tx r false X2 $$ Hw with ⟨%Hhok2, Hw⟩
    obtain ⟨B2, hB2⟩ := Option.isSome_iff_exists.1 hrl2
    have hB2' : X2.t.bs !! (tx.[Tx, go!"root"]) = some B2 := by
      rw [← hB2, Hhok2.1]; rfl
    icases wtxW_bkt_acc K tx r false X2 _ B2 hB2' $$ Hw with ⟨Ho, Hwb⟩
    isimp only [objOwn] at Ho
    icases Ho with ⟨HIB, Htxf, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
    try wp_auto
    wp_method_call; wp_call
    try wp_auto
    wp_apply wp_RootPage $$ [Hib] as Hib
    · iframe
    ihave Hw := Hwb $$ [HIB Htxf Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
    · simp only [objOwn]; iframe
    icases cm_meta_acc K tx r false X2 $$ Hw with ⟨Hme, Hmv, Hwb⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hmv with ⟨Hmv, %Hmvn2⟩
    try wp_auto
    wp_apply wp_RootBucket
    icases cm_meta_root _ _ Hmvn2 $$ Hmv with ⟨Hrt, Hmvb⟩
    wp_apply wp_SetRootPage $$ [Hrt] as Hrt
    · iframe #; iframe
    ihave Hmv := Hmvb $$ %_ Hrt
    ihave Hw := Hwb $$ %_ Hme Hmv
    try wp_auto
    -- the old freelist page freed, when the committed state has one
    have hfl2 : metaFlpg X2.t.mv = w2.C.flpg := by
      rw [hC2, ← Hmeta.2.2.2.2, ← hmv1, hmv2]; rfl
    icases cm_meta_acc K tx r false _ $$ Hw with ⟨Hme, Hmv, Hwb⟩
    simp only [WX.withMv_tt, WX.withMv_mv]
    try wp_auto
    wp_apply wp_Freelist $$ [Hmv] as Hmv
    · iframe #; iframe
    ihave Hw := Hwb $$ %_ Hme Hmv
    try wp_auto
    by_cases hnf : X2.t.mv.freelist' = W64 18446744073709551615
    · -- no synced freelist page (`NoFreelistSync`'s files): nothing to free
      have hC2fl : w2.C.flpg = none := by
        rw [← hfl2]; unfold metaFlpg pgidNoFreelist; rw [hnf]; rfl
      rw [decide_eq_true hnf]
      try wp_auto
      icases cm_db_acc K tx r false _ $$ Hw with ⟨%Hrdb, Hdbp, Hwb⟩
      ihave #Hfix2 := Hfix
      iunfold dbFixed at Hfix2
      icases Hfix2 with ⟨-, -, -, -, -, -, -, -, ⟨%nfs, #Hnfs⟩, -⟩
      try wp_auto
      cases nfs
      · -- `commitFreelist`
        ihave Hw := Hwb $$ Hdbp
        try wp_auto
        sorry
      · -- `NoFreelistSync`: `tx.meta.SetFreelist(PgidNoFreelist)`
        ihave Hw := Hwb $$ Hdbp
        try wp_auto
        sorry
    · -- the synced freelist page `f` freed (`store_free_fl`): the writer side's weaker invariant
      -- from here on (batch 44's flagged `wdbW'`)
      rw [decide_eq_false hnf]
      try wp_auto
      sorry
  · -- `spill` failed: log, roll back, return the error
    obtain ⟨ii, rfl⟩ : ∃ ii, err1 = GoInterface.ok ii := by
      cases err1 with
      | nil => exact absurd rfl He1
      | ok ii => exact ⟨ii, rfl⟩
    obtain ⟨hC2, -, -, htt2, -, hrl2, hmv2⟩ := Hsp
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply wp_boltLog li _ _ [W8 118] _ [GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok' [Hsl] [] [] as Hsl -
    · iframe
    · try simp only [List.zip_cons_cons, List.zip_nil_left]
      isplitl
      · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe1
      · iempintro
    try wp_auto
    -- Gap 7: `spill`'s error post says nothing of the records but their view's pages
    have hwr2 : X2.t.t.writable' = true := by rw [htt2, htt1]; exact hwr
    have htx2 : X2.t.mv.txid' = W64 ((w2.C.txid + 1 : Nat) : Int) := by
      have h1 : X2.t.mv.txid' = X.t.mv.txid' := by rw [hmv2, hmv1]
      have h2 : X.v.txid + 1 = X.t.mv.txid'.toNat := Hf.1.1.2.2.2.1
      have h3 : X.v.txid = w.C.txid := by rw [Hwok.2.2]; rfl
      rw [h1, hC2]
      apply BitVec.eq_of_toNat_eq
      rw [← h2, h3]
      have h64 : w.C.txid + 1 < 2 ^ 64 := Hwok.1.2.2.2.2.2.2.1
      word
    imod cm_excl_update K r X1 X2 _ $$ Hex with Hex
    ihave Hex : cmExcl K r X2 (treeData w2.C) $$ [Hex]
    · rw [hC2]; iexact Hex
    icases Hres with (⟨Hw, Hwdb⟩ | ⟨Hw, Hwdb⟩)
    · icases (cm_keep_pure (cm_wdbW_ok K tx X2.v w2)) $$ Hwdb with ⟨Hwdb, %Hw2ok⟩
      ihave Hend := cm_wtxEnd_live K tx r X2 w2 hwr2 hrl2 $$ [Hw Hwdb Hex]
      · iframe; iframe #
      wp_apply wp_rollback K tx r X2 (wLive X2.v w2.C) w2
        ⟨X2.v, w2.C.txid + 1, false, true, rfl, htx2,
          ⟨fun _ => by rw [Hw2ok.2.1]; simp, fun _ => rfl⟩, fun _ => rfl, fun h => absurd h (by simp)⟩
        $$ [Hend] as Hdone
      · iexact Hend
      cm_return
    · icases (cm_keep_pure (cm_wdbLost_ok K tx X2.v w2)) $$ Hwdb with ⟨Hwdb, %Hw2ok⟩
      ihave Hend := cm_wtxEnd_lost K tx r X2 w2 hwr2 hrl2 $$ [Hw Hwdb Hex]
      · iframe; iframe #
      wp_apply wp_rollback K tx r X2 _ w2
        ⟨X2.v, w2.C.txid + 1, false, false, rfl, htx2,
          ⟨fun h => absurd h (by simp), fun h => absurd Hw2ok.2 h⟩, fun h => absurd h (by simp),
          fun h => absurd h (by simp)⟩
        $$ [Hend] as Hdone
      · iexact Hend
      cm_return

end proof

end bbolt
end EtcdGrove
end Perennial
