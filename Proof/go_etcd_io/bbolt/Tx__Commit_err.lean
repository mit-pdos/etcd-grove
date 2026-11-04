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
public import Proof.go_etcd_io.bbolt.Commit.TailPure
public import Proof.go_etcd_io.bbolt.Commit.TailDefs
public import Proof.go_etcd_io.bbolt.Commit.TailSlots
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

set_option maxHeartbeats 1600000 in
theorem Tx.Commit_err.wp_proof'
    (wp_Assert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (wp_ID : Tx.ID.spec (GF := GF) (hG := hG))
    (wp_rebalance : Bucket.rebalance.spec (GF := GF) (hG := hG))
    (wp_spill : Bucket.spill.spec (GF := GF) (hG := hG))
    (wp_rollback : Tx.rollback.spec (GF := GF) (hG := hG))
    (wp_close : Tx.close_w.spec (GF := GF) (hG := hG))
    (wp_commitFreelist : Tx.commitFreelist.spec (GF := GF) (hG := hG))
    (wp_grow : DB.grow.spec (GF := GF) (hG := hG))
    (wp_write : Tx.write_ext.spec (GF := GF) (hG := hG))
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
  obtain ⟨hrbOK, hreach1, hflv1, htt1, hmv1, hbm1⟩ := Hrb
  have hv1 : X1.v = X.v := hrbOK.2.2.1
  rw [← hv1]
  have hmap1 : X1.t.mv.pgid'.toNat * 4096 ≤ mapLen (w.withFl fl1).ms := by
    rw [hmv1, show (w.withFl fl1).ms = w.ms from rfl, Hmeta.2.2.2.1]
    exact Hwok.1.2.2.2.2.2.2.2.2.1 _ _ Hwok.2.1
  -- the spill's start: the committed tree, the mark, the root bucket's children (`wrFacts` and
  -- `gensOK` of `X`, the root bucket's `bm` kept by `rebalance`)
  have hroot1 : ∀ B0, X1.t.bs !! X1.rl = some B0 → (∀ k c, B0.bm !! k = some c → c ≠ X1.rl) ∧
      ∀ k k' c, B0.bm !! k = some c → B0.bm !! k' = some c → k = k' :=
    cm_root_children T X X1 Hf.2.2.2.1 Hf.2.2.2.2.2.2 hrbOK.2.2.2.2.1 hbm1
  have hstart1 : spillStartOK X1 (w.withFl fl1) :=
    ⟨Hflv.2.2, by rw [hmv1, Hmeta.2.2.2.1]; exact Nat.le_refl _, hroot1⟩
  -- the writer's txid below `2 ^ 63` (the receipts' budget, maintainer 12, item 1)
  icases wdbW_txid_lt K tx _ (w.withFl fl1) $$ [Hwdb] with ⟨Hwdb, %Htxl⟩
  · iframe; iframe #
  have hopg : X1.t.mv.pgid'.toNat = w.C.hwm := by rw [hmv1, Hmeta.2.2.2.1]
  have htx63 : X1.t.mv.txid'.toNat < 2 ^ 63 := by
    rw [hmv1, ← Hf.1.1.2.2.2.1, show X.v.txid = w.C.txid by rw [Hwok.2.2]; rfl]
    exact Htxl
  wp_apply wp_spill K tx r false X1 (w.withFl fl1) (spillPre_of_rebalOK X X1 w.fl fl1 _ hrbOK)
    hreach1 hmap1 hflv1 hstart1 htx63 $$ [Hw Hwdb] as %err1 Hsp
  · iframe
  cases lg with
  | nil => iexfalso; unfold dbLogger boltLogger; iexact Hlgok
  | ok li =>
  ihave #Hlgok' : boltLogger (GF := GF) (.ok li) $$ []
  · unfold dbLogger; iexact Hlgok
  icases Hsp with (⟨%He1, %X2, %w2, Hw, Hwdb, %Hsp⟩ | ⟨%He1, #Hfe1, %X2, %w2, %st, %Hsp, Hres⟩)
  · -- spilled
    subst He1
    obtain ⟨hspOK, hC2, hderef2, hfresh2, hreach2, hmap2, hbufs2, htt2, hrl2e, hrl2, hmv2⟩ := Hsp
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
      -- the freelist's branches join before `grow` (`cmTailOK`), or return an error rolled back
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(
          (⌜v = executeVal⌝ ∗ err_ptr ↦ GoInterface.nil ∗ lg_ptr ↦ GoInterface.ok li ∗ tx_ptr ↦ tx ∗
            ∃ (Xt : WX) (wt : WDb), wtxW K tx r false Xt ∗ wdbW K tx Xt.v wt ∗
              cmExcl K r Xt (treeData wt.C) ∗ ⌜cmTailOK T.cur T.base Xt wt X1.t.mv.pgid'⌝) ∨
          (⌜v = returnVal #()⌝ ∗ lg_ptr ↦ GoInterface.ok li ∗ tx_ptr ↦ tx ∗
            ∃ e : GoInterface, err_ptr ↦ e ∗ ⌜e ≠ GoInterface.nil⌝ ∗ fmtErrorOk e ∗ txDoneDef tx))))
        $$ [Hwb Hdbp Hwdb Hex err Hlgp tx]
      · cases nfs
        · -- `commitFreelist`
          ihave Hw := Hwb $$ Hdbp
          try wp_auto
          simp only [WX.withMv_withMv, WX.withMv_mv]
          generalize hX3 : X2.withMv ({ X2.t.mv with
            root' := ({ X2.t.mv.root' with root' := B2.ib.root' } : InBucket) } : Meta) = X3
          have hv3 : X3.v = X2.v := by rw [← hX3]; rfl
          have htt3 : X3.t.t = X2.t.t := by rw [← hX3]; rfl
          have hrl3 : (X3.t.bs !! X3.rl).isSome := by rw [← hX3]; exact hrl2
          have hwr3 : X3.t.t.writable' = true := by rw [htt3, htt2, htt1]; exact hwr
          have htx3 : X3.t.mv.txid' = w2.wtxid := by
            have h1 : X3.t.mv.txid' = X.t.mv.txid' := by rw [← hX3]; simp only [WX.withMv_mv]; rw [hmv2, hmv1]
            have h2 : X.v.txid + 1 = X.t.mv.txid'.toNat := Hf.1.1.2.2.2.1
            have h3 : X.v.txid = w.C.txid := by rw [Hwok.2.2]; rfl
            rw [h1]
            unfold WDb.wtxid
            rw [hC2]
            apply BitVec.eq_of_toNat_eq
            rw [← h2, h3]
            have h64 : w.C.txid + 1 < 2 ^ 64 := Hwok.1.2.2.2.2.2.2.1
            word
          have hmap3 : X3.t.mv.pgid'.toNat * 4096 ≤ mapLen w2.ms := by
            rw [← hX3]; exact hmap2
          have hderefKeep : ∀ Xd b, derefRel X3 Xd → (Xd.rebase b).t.t.writable' = true ∧
              ((Xd.rebase b).t.bs !! (Xd.rebase b).rl).isSome := fun Xd b hd =>
            cm_derefKeep X3 Xd b hd hwr3 hrl3
          have hrb1 : iprop(K.full (GF := GF) ∗ cmExcl K r X3 (treeData w2.C)) ∗
              wtxW K tx r false X3 ∗ wdbW' false K tx X3.v w2 ⊢
              |==> wtxEnd K tx r X3 (wLive X3.v w2.C) w2 := by
            iintro ⟨⟨#Hfu, Hx⟩, Hw, Hd⟩
            ihave Hd := wdbW'_wdbW K tx X3.v w2 $$ Hd
            imodintro
            iapply cm_wtxEnd_live K tx r X3 w2 hwr3 hrl3
            iframe; iframe #
          have hrb2 : ∀ (X' : WX) (w' : WDb), (∃ Xd b, derefRel X3 Xd ∧ X' = Xd.rebase b) →
              w'.C = w2.C → w'.fl = w2.fl →
              iprop(K.full (GF := GF) ∗ cmExcl K r X3 (treeData w2.C)) ∗
                wtxLost K tx r false X' ∗ wdbLost' false K tx X'.v w' ⊢
              |==> wtxEnd K tx r X' (some X'.v, some (w'.C.txid + 1), false, false) w' := by
            rintro X' w' ⟨Xd, b, hd, rfl⟩ hC _
            obtain ⟨hw', hr'⟩ := hderefKeep Xd b hd
            iintro ⟨⟨#Hfu, Hx⟩, Hw, Hd⟩
            ihave Hd := wdbLost'_wdbLost K tx _ w' $$ Hd
            imod cm_excl_update K r X3 (Xd.rebase b) _ $$ Hx with Hx
            imodintro
            iapply cm_wtxEnd_lost K tx r (Xd.rebase b) w' hw' hr'
            rw [hC]; iframe; iframe #
          rw [show X2.v = X3.v from hv3.symm]
          imod cm_excl_update K r X1 X3 _ $$ Hex with Hex
          ihave Hex : cmExcl K r X3 (treeData w2.C) $$ [Hex]
          · rw [hC2]; iexact Hex
          icases (cm_keep_pure (cm_wdbW_bounds K tx X3.v w2)) $$ Hwdb with ⟨Hwdb, %Hbd2⟩
          icases (cm_keep_pure (cm_wdbW_ok K tx X3.v w2)) $$ Hwdb with ⟨Hwdb, %Hw2ok⟩
          ihave Hwdb := wdbW_wdbW' false K tx X3.v w2 $$ Hwdb
          wp_apply wp_commitFreelist false K tx r X3 w2 iprop(K.full ∗ cmExcl K r X3 (treeData w2.C))
            htx3 hmap3 (by rw [← hX3]; exact hderef2) (by rw [← hX3]; exact hfresh2)
            (liveReach_congr X2 X3 (by rw [← hX3]; rfl) (by rw [← hX3]; rfl) (by rw [← hX3]; rfl)
              (by rw [← hX3]; rfl) hreach2) (cm_allIds_lt w2 Hw2ok.1 Hbd2.1 Hbd2.2) hrb1 hrb2
            $$ [Hex Hw Hwdb] as %err2 Hcf
          · iframe; iframe #
          icases Hcf with (⟨%He2, %X4, %w4, %id4, %p4, ⟨-, Hex⟩, Hw, Hwdb, %Hal⟩ |
            ⟨%He2, #Hfe2, Hdone⟩)
          · -- joins the tail
            ihave Hwdb := wdbW'_wdbW K tx _ w4 $$ Hwdb
            icases (cm_keep_pure (cm_wdbW_ok K tx _ w4)) $$ Hwdb with ⟨Hwdb, %Hw4ok⟩
            obtain ⟨htt4, hrl4, htx4⟩ := allocRes_keep _ _ _ _ _ _ _ _ Hal.1
            have htt5 : X4.t.t = X.t.t := by rw [htt4, htt3, htt2, htt1]
            imod cm_excl_update K r X3 (X4.setFlPage id4 (flPageBytes w4.fl id4 (flCount w2.fl))) _
              $$ Hex with Hex
            ihave Hex : cmExcl K r (X4.setFlPage id4 (flPageBytes w4.fl id4 (flCount w2.fl)))
                (treeData w4.C) $$ [Hex]
            · rw [Hal.2.1]; iexact Hex
            subst He2
            try wp_auto
            ileft
            isplitr
            · ipureintro; rfl
            iframe err Hlgp tx
            iexists X4.setFlPage id4 (flPageBytes w4.fl id4 (flCount w2.fl)), w4
            rw [show (X4.setFlPage id4 (flPageBytes w4.fl id4 (flCount w2.fl))).v = X4.v from rfl]
            iframe
            ipureintro
            refine ⟨?_, ?_, ?_, Hal.2.2.1, ?_, ?_, ?_, ?_, Hw4ok.1, ?_, ?_⟩
            · show X4.t.t.writable' = true; rw [htt5]; exact hwr
            · show (X4.t.bs !! X4.rl).isSome = true; rw [hrl4]; exact hrl3
            · show X4.t.mv.txid' = w4.wtxid
              rw [htx4, htx3]; unfold WDb.wtxid; rw [Hal.2.1]
            · rw [Hal.2.1, hC2]; exact hopg.symm
            · show X4.t.t.commitHandlers' = slice.nil; rw [htt5]; exact Hf.2.2.2.2.2.1
            · show X4.t.t.meta' ≠ null; rw [htt5]; exact Hmvn
            · rw [Hal.2.1]; exact hC2fl
            · rw [Hal.2.1, hC2]; exact hbase
            · -- OPEN (U10k): the publish's facts from spill's, rebalance's and commitFreelist's posts
              sorry
          · -- `commitFreelist` failed (rolled back): log, return the error
            obtain ⟨ii, rfl⟩ : ∃ ii, err2 = GoInterface.ok ii := by
              cases err2 with
              | nil => exact absurd rfl He2
              | ok ii => exact ⟨ii, rfl⟩
            irename Hfe2 => Hfe1
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
            iright
            isplitr
            · ipureintro; rfl
            iframe; iframe #
            ipureintro; exact He2
        · -- `NoFreelistSync`: `tx.meta.SetFreelist(PgidNoFreelist)`
          ihave Hw := Hwb $$ Hdbp
          try wp_auto
          simp only [WX.withMv_withMv]
          imod cm_excl_update K r X1 (X2.withMv ({ X2.t.mv with
            root' := ({ X2.t.mv.root' with root' := B2.ib.root' } : InBucket),
            freelist' := W64 18446744073709551615 } : Meta)) _ $$ Hex with Hex
          icases cm_meta_acc K tx r false _ $$ Hw with ⟨Hme, Hmv, Hwb⟩
          isimp only [WX.withMv_tt, WX.withMv_mv] at Hme Hmv Hwb
          try wp_auto
          wp_apply wp_SetFreelist $$ [Hmv] as Hmv
          · iframe #; iframe
          ihave Hw := Hwb $$ %_ Hme Hmv
          simp only [WX.withMv_withMv]
          generalize hX3 : X2.withMv ({ X2.t.mv with
            root' := ({ X2.t.mv.root' with root' := B2.ib.root' } : InBucket),
            freelist' := W64 18446744073709551615 } : Meta) = X3
          have hv3 : X3.v = X2.v := by rw [← hX3]; rfl
          have htt3 : X3.t.t = X2.t.t := by rw [← hX3]; rfl
          ihave Hex : cmExcl K r X3 (treeData w2.C) $$ [Hex]
          · rw [hC2]; iexact Hex
          icases (cm_keep_pure (cm_wdbW_ok K tx _ w2)) $$ Hwdb with ⟨Hwdb, %Hw2ok⟩
          try wp_auto
          ileft
          isplitr
          · ipureintro; first | rfl | trivial
          iframe err Hlgp tx
          iexists X3, w2
          rw [hv3]
          iframe
          ipureintro
          have htt5 : X3.t.t = X.t.t := by rw [htt3, htt2, htt1]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hC2fl, Hw2ok.1, ?_, ?_⟩
          · rw [htt5]; exact hwr
          · rw [← hX3]; exact hrl2
          · have h1 : X3.t.mv.txid' = X.t.mv.txid' := by
              rw [← hX3]; simp only [WX.withMv_mv]; rw [hmv2, hmv1]
            have h2 : X.v.txid + 1 = X.t.mv.txid'.toNat := Hf.1.1.2.2.2.1
            have h3 : X.v.txid = w.C.txid := by rw [Hwok.2.2]; rfl
            rw [h1]
            unfold WDb.wtxid
            rw [hC2]
            apply BitVec.eq_of_toNat_eq
            rw [← h2, h3]
            have h64 : w.C.txid + 1 < 2 ^ 64 := Hwok.1.2.2.2.2.2.2.1
            word
          · rw [← hX3]; exact hmap2
          · rw [hC2]; exact hopg.symm
          · rw [htt5]; exact Hf.2.2.2.2.2.1
          · rw [htt5]; exact Hmvn
          · rw [hC2]; exact hbase
          · -- OPEN (U10k): the publish's facts from spill's and rebalance's posts
            sorry
      iintro %v Hv
      icases Hv with (⟨%hv, err, Hlgp, tx, %Xt, %wt, Hw, Hwdb, Hex, %Htl⟩ |
        ⟨%hv, Hlgp, tx, %e1, err, %He1, #Hfe1, Hdone⟩)
      · subst hv
        try wp_auto
        -- `grow`, if the high-water mark moved up
        obtain ⟨hwrt, hrlt, htxt, hmapt, hhwmt, hcht, hmpt, hflt, hwokt, hbt, hpre⟩ := Htl
        icases cm_meta_acc K tx r false Xt $$ Hw with ⟨Hme, Hmv, Hwb⟩
        try wp_auto
        wp_apply wp_Pgid $$ [Hmv] as Hmv
        · iframe #; iframe
        ihave Hw := Hwb $$ %Xt.t.mv Hme Hmv
        have eXt : Xt.withMv Xt.t.mv = Xt := rfl
        rw [eXt]
        try wp_auto
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun v => iprop(
            (⌜v = executeVal⌝ ∗ err_ptr ↦ GoInterface.nil ∗ lg_ptr ↦ GoInterface.ok li ∗
              tx_ptr ↦ tx ∗ wtxW K tx r false Xt ∗ cmExcl K r Xt (treeData wt.C) ∗
              ∃ wg : WDb, wdbW K tx Xt.v wg ∗ ⌜wdbGrown wt wg⌝) ∨
            (⌜v = returnVal #()⌝ ∗ lg_ptr ↦ GoInterface.ok li ∗ tx_ptr ↦ tx ∗
              ∃ e : GoInterface, err_ptr ↦ e ∗ ⌜e ≠ GoInterface.nil⌝ ∗ fmtErrorOk e ∗
                txDoneDef tx))))
          $$ [Hw Hwdb Hex err Hlgp tx]
        · by_cases hg : uint.Z X1.t.mv.pgid' < uint.Z Xt.t.mv.pgid'
          · rw [decide_eq_true hg]
            try wp_auto
            wp_apply errors.New.wp_proof as %e0 -
            try wp_auto
            icases cm_meta_acc K tx r false Xt $$ Hw with ⟨Hme, Hmv, Hwb⟩
            try wp_auto
            wp_apply wp_Pgid $$ [Hmv] as Hmv
            · iframe #; iframe
            ihave Hw := Hwb $$ %Xt.t.mv Hme Hmv
            rw [eXt]
            ihave #Hfix3 := Hfix
            iunfold dbFixed at Hfix3
            icases Hfix3 with ⟨#Hps, -⟩
            icases cm_db_acc K tx r false Xt $$ Hw with ⟨-, Hdbp, Hwb⟩
            try wp_auto
            icases (cm_keep_pure (wdbW_mapLen_le K tx Xt.v wt)) $$ Hwdb with ⟨Hwdb, %Hml⟩
            ihave Hwdb := wdbW_wdbW' false K tx Xt.v wt $$ Hwdb
            have hn : Xt.t.mv.pgid'.toNat < 2 ^ 36 := by omega
            have hz1 : 0 ≤ sint.Z ((Xt.t.mv.pgid' + W64 1) * W64 4096) := by word
            have hz2 : sint.Z ((Xt.t.mv.pgid' + W64 1) * W64 4096) + 0x1000000 < 2 ^ 63 := by word
            have hz3 : sint.Z ((Xt.t.mv.pgid' + W64 1) * W64 4096) % 4096 = 0 := by word
            wp_apply wp_grow false K tx Xt.v wt _ hz1 hz2 hz3 $$ [Hwdb]
              as %err3 ⟨%wg, Hwdb, %Hgr, Hres⟩
            · iframe #; iframe
            ihave Hwdb := wdbW'_wdbW K tx Xt.v wg $$ Hwdb
            icases (cm_keep_pure (cm_wdbW_ok K tx Xt.v wg)) $$ Hwdb with ⟨Hwdb, %Hwgok⟩
            icases Hres with (%He3 | ⟨%He3, #Hfe3⟩)
            · subst He3
              ihave Hw := Hwb $$ Hdbp
              try wp_auto
              ileft
              isplitr
              · ipureintro; first | rfl | trivial
              iframe
              ipureintro; exact Hgr
            · -- `grow` failed: log, roll back, return the error
              obtain ⟨ii, rfl⟩ : ∃ ii, err3 = GoInterface.ok ii := by
                cases err3 with
                | nil => exact absurd rfl He3
                | ok ii => exact ⟨ii, rfl⟩
              ihave Hw := Hwb $$ Hdbp
              try wp_auto
              icases cm_meta_acc K tx r false Xt $$ Hw with ⟨Hme, Hmv, Hwb⟩
              try wp_auto
              wp_apply wp_Pgid $$ [Hmv] as Hmv
              · iframe #; iframe
              ihave Hw := Hwb $$ %Xt.t.mv Hme Hmv
              rw [eXt]
              icases cm_db_acc K tx r false Xt $$ Hw with ⟨-, Hdbp, Hwb⟩
              try wp_auto
              ihave Hw := Hwb $$ Hdbp
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %sl ⟨Hsl, -⟩
              try wp_auto
              wp_apply wp_boltLog li _ _ [W8 100, W8 100, W8 118] _
                [interface.mkOk Pgid.ty #Xt.t.mv.pgid', interface.mkOk go.int #(W64 4096),
                  GoInterface.ok ii] _ iprop(True) _
                (by decide) (by decide) rfl $$ Hlgok' [Hsl] [] [] as Hsl -
              · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
                  show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set_cons_succ,
                  List.set_cons_zero]
                iexact Hsl
              · simp only [List.zip_cons_cons, List.zip_nil_left, Iris.BI.BigSepL.bigSepL_cons,
                  Iris.BI.BigSepL.bigSepL_nil]
                isplitr
                · iapply logArgOk_of_argWf; exact pgid_argWf _
                isplitr
                · iapply logArgOk_int
                isplitr
                · iapply logArgOk_of_fmtErrorOk
                  · simp [methodVerbs]
                  iexact Hfe3
                iempintro
              try wp_auto
              have htxg : Xt.t.mv.txid' = W64 ((wg.C.txid + 1 : Nat) : Int) := by
                rw [htxt, Hgr.1]; rfl
              ihave Hex : cmExcl K r Xt (treeData wg.C) $$ [Hex]
              · rw [Hgr.1]; iexact Hex
              ihave Hend := cm_wtxEnd_live K tx r Xt wg hwrt hrlt $$ [Hw Hwdb Hex]
              · iframe; iframe #
              wp_apply wp_rollback K tx r Xt (wLive Xt.v wg.C) wg
                ⟨Xt.v, wg.C.txid + 1, false, true, rfl, htxg,
                  ⟨fun _ => by rw [Hwgok.2.1]; simp, fun _ => rfl⟩, fun _ => rfl,
                  fun h => absurd h (by simp)⟩
                $$ [Hend] as Hdone
              · iexact Hend
              try wp_auto
              iright
              isplitr
              · ipureintro; first | rfl | trivial
              iframe
              iframe #
              ipureintro; exact fun h => nomatch h
          · rw [decide_eq_false hg]
            try wp_auto
            ileft
            isplitr
            · ipureintro; first | rfl | trivial
            iframe
            ipureintro; exact wdbGrown_refl wt
        iintro %v Hv
        icases Hv with (⟨%hv, err, Hlgp, tx, Hw, Hex, %wg, Hwdb, %Hgr⟩ |
          ⟨%hv, Hlgp, tx, %e1, err, %He1, #Hfe1, Hdone⟩)
        · subst hv
          try wp_auto
          -- `write`: the dirty pages, possibly past the file's end
          wp_apply time.wp_Now as %t2 -
          try wp_auto
          have hpre' := cmPubPre_congr T.cur Xt wt wg Hgr.1 Hgr.2.1 hpre
          icases (cm_keep_pure (cm_wdbW_ok K tx Xt.v wg)) $$ Hwdb with ⟨Hwdb, %Hwgok⟩
          iunfold wdbW at Hwdb
          icases Hwdb with ⟨Hwl, -⟩
          icases (cm_keep_pure (cm_wdbLive_mapLen K.B K.db K.p K.sp K.t0 tx _ wg)) $$ Hwl
            with ⟨Hwl, %Hml⟩
          have hms : wg.ms = some (Xt.v.base, mapLen wg.ms) := Hwgok.2.1
          have hmapl : Xt.t.mv.pgid'.toNat * 4096 ≤ mapLen wg.ms := by rw [Hgr.2.2.1]; exact hmapt
          obtain ⟨hbok, hsub, hW, hlen, hinW⟩ :=
            cm_write_pre T.cur Xt wg _ _ hpre' Hwgok.1 hms hmapl
          have hsz63 : wg.m.size < 2 ^ 63 := Hwgok.1.2.2.2.2.2.2.2.2.2.2.2.2.1
          wp_apply cm_write_step wp_write K tx r Xt (wLive Xt.v wg.C) wg Xt.v.base (mapLen wg.ms) hms
            (Hwgok.1.1 _ _ hms) hsz63 (by omega) hpre'.1 hbok hpre'.2.2.1 hsub hW hlen hinW
            $$ [Hw Hwl] as %err4 ⟨%pml, %m', %wb', %Hm', Hw, Hres⟩
          · iframe
          have hsub' : ∀ s ∈ bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms),
              s ∈ wg.W := by
            intro s hs
            rcases List.mem_append.1 hs with h | h
            · exact hsub s h
            · exact ((mem_cmTail _ _ _ s).1 h).2.1
          have hmax : m'.size ≤ max wg.m.size (mapLen wg.ms) := Hm'.2.1
          icases Hres with (⟨%He4, %Hch, Hwl, HSB⟩ | ⟨%He4, #Hfe4, Hwl⟩)
          · subst He4
            obtain ⟨-, -, -, -, hroot, hflp, h2hwm, -, -, Pg, hpg⟩ := hpre'
            have hinSB : ∀ s ∈ (bufSlots Xt.t.bufs), 4096 * (s + 1) ≤ mapLen wg.ms ∧ 4096 * (s + 1) ≤ m'.size := by
              intro s hs
              refine ⟨?_, Hch.1 s hs⟩
              obtain ⟨id, pg, hp, h1, h2⟩ := (mem_bufSlots Xt.t.bufs s).1 hs
              have h4 := (hbok id pg hp).2.2.2
              have h5 : 4096 * (mapLen wg.ms / 4096) ≤ mapLen wg.ms := Nat.mul_div_le _ _
              omega
            icases cm_slots_split K.B K.db K.p K.sp K.t0 tx (wLive Xt.v wg.C)
              (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)) Xt.v.base (mapLen wg.ms) (bufSlots Xt.t.bufs) wb'
              (pubP wg Xt Pg) hms
              (fun s hs hSB => by
                rcases List.mem_append.1 hs with h | h
                · exact ((mem_cmTail _ _ _ s).1 h).2.2.2 hSB
                · exact ((mem_wMinus _ _ s).1 h).2 (List.mem_append_left _ hSB))
              hinSB (fun s hs => Hm'.2.2.2 s (List.mem_append_left _ hs) (Hch.1 s hs))
              $$ [Hwl HSB] with ⟨Hwl, HS⟩
            · iframe
            -- `StrictMode` is off
            ihave #Hfix4 := Hfix
            iunfold dbFixed at Hfix4
            icases Hfix4 with ⟨-, -, -, -, #Hsm, -⟩
            icases cm_db_acc K tx r false _ $$ Hw with ⟨-, Hdbp, Hwb⟩
            try wp_auto
            ihave Hw := Hwb $$ Hdbp
            -- `writeMeta`: the commit point
            obtain ⟨hcp, hokP⟩ := cm_pub_ok T.cur Xt wg Xt.v.base (mapLen wg.ms) Pg m' m' wb'
              (cmPubPre_congr T.cur Xt wt wg Hgr.1 Hgr.2.1 hpre) hpg
              (by rw [htxt]; unfold WDb.wtxid; rw [Hgr.1]) Hwgok.1 hms hmapl
              (by rw [Hgr.1]; exact hflt) Hm' ⟨rfl, rfl⟩ Hch.1 Hch.2
            unfold cmExcl
            icases Hex with ⟨Hrwl, Hcls, Hagr, Hstq⟩
            ihave Hstq : ghostVar K.B.st (1 : Qp).half.half (treeData ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C) $$ [Hstq]
            · rw [WDb.reslot.proj_C, WDb.reslot.proj_C, Hgr.1]; iexact Hstq
            ihave Hau' : commitAU K γ.ns (treeData ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C) T.cur Q $$ [Hau]
            · unfold commitAU
              rw [WDb.reslot.proj_C, WDb.reslot.proj_C, Hgr.1, ← hbt]
              unfold boltState at *
              rw [hB]
              iexact Hau
            ihave Hfb : fbTok K.B ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).fl ((some Xt.v, some (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C.txid + 1), false, true) : WSt)
                ∅ $$ []
            · rw [WDb.reslot.proj_C, WDb.reslot.proj_C, WDb.reslot.proj_fl, WDb.reslot.proj_fl]
              iapply (fbTok_of_wdbOK (GF := GF) K.B wg Hwgok.1 _ ∅)
            have haddr : 0 < (Xt.clearPages pml).t.t.meta'.addr := by
              -- OPEN (U10k): `tx.meta`'s pointer positive (`writeMeta`'s premise); not derivable
              -- from `≠ null` (`Loc.addr` is an `Int`)
              sorry
            have h3 := Hwgok.1.2.2.1
            have h9 := Hwgok.1.2.2.2.2.2.2.2.2.1 _ _ hms
            wp_apply cm_meta_step wp_writeMeta K tx r (Xt.clearPages pml) Xt.v ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)) Xt.v.base
              (mapLen wg.ms) γ.ns ((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) wb' Pg T.cur Q ∅ hms
              (by rw [WDb.reslot.proj_m, WDb.reslot.proj_m, Hm'.2.2.1]; exact Hwgok.1.1 _ _ hms)
              hroot hflp haddr (by rw [WDb.reslot.proj_m, WDb.reslot.proj_m]; omega) (by omega) hcp
              $$ [Hw Hwl Hstq HS Hau' Hfb] as %err5 ⟨%m'', %Hm'', Hw, Herr, Hpost⟩
            · iframe
            icases Herr with (%He5 | ⟨%He5, #Hfe5⟩)
            · subst He5
              icases Hpost with (⟨Hwl, Hstq, HQ⟩ | ⟨%Hne, -⟩)
              · try wp_auto
                wp_apply time.wp_Since as %d5 -
                try wp_auto
                icases cm_stats_acc K tx r false _ $$ Hw with ⟨-, -, Hst5, Hwb⟩
                wp_apply wp_IncWriteTime K tx r false 1 $$ [Hst5] as %_ Hst5
                · iframe; iframe #
                ihave Hw := Hwb $$ Hst5
                try wp_auto
                have hokF := (cm_pub_ok T.cur Xt wg Xt.v.base (mapLen wg.ms) Pg m' m'' wb'
                  (cmPubPre_congr T.cur Xt wt wg Hgr.1 Hgr.2.1 hpre) hpg
                  (by rw [htxt]; unfold WDb.wtxid; rw [Hgr.1]) Hwgok.1 hms hmapl
                  (by rw [Hgr.1]; exact hflt) Hm' Hm'' Hch.1 Hch.2).2
                icases Hagr with ⟨%c5, Hagr⟩
                imod ghostVar_update (c5, TxX.wr ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv)))
                  r.n.v _ $$ Hagr with Hagr
                have hDn : treeData ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).withC (pubC ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C (Xt.clearPages pml).t.mv Pg)).C = T.cur := hcp.2.2.2.1
                wp_apply wp_close K tx r ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv)) ((some Xt.v, some (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C.txid + 1), true, true) : WSt) ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).withC (pubC ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C (Xt.clearPages pml).t.mv Pg))
                  ⟨Xt.v, _, true, true, rfl, Or.inl rfl,
                    ⟨fun _ => by show wg.ms ≠ none; rw [hms]; simp, fun _ => rfl⟩, fun _ => rfl⟩
                  $$ [Hw Hwl Hrwl Hcls Hagr Hstq] as ⟨Hdone, Hch5⟩
                · unfold wtxEnd
                  iframe #
                  isplitl [Hw]
                  · ileft; iexact Hw
                  isplitl [Hwl]
                  · simp only [WDb.reslot.proj_C, WDb.reslot.proj_W, WDb.reslot.proj_wb,
                      WDb.reslot.proj_m, WDb.reslot_reslot, WX.clearPages_mv]
                    iexact Hwl
                  iframe Hrwl Hcls
                  isplitl [Hagr]
                  · iexists c5; iexact Hagr
                  isplitl [Hstq]
                  · rw [hDn]; iexact Hstq
                  ipureintro
                  exact ⟨hokF, hwrt, hrlt⟩
                -- no commit handler
                ihave Hch5 : tx.[Tx, go!"commitHandlers"] ↦ (slice.nil : GoSlice) $$ [Hch5]
                · rw [← hcht]; iexact Hch5
                try wp_auto
                ihave IH : iprop("i" ∷ i_ptr ↦ (W64 0)) $$ [i]
                · iframe
                wp_for IH
                wp_if_destruct
                · exfalso
                  rw [hcht] at Hif
                  simp [slice.nil] at Hif
                · wp_bind (App (Val #_) (Val #()))
                  iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ GoInterface.nil)))
                    $$ [err HtxId Hlgp]
                  · iapply Hdf $$ [] err HtxId Hlgp
                    ileft; ipureintro; rfl
                  iintro %vret ⟨%hvret, err⟩
                  subst hvret
                  wp_auto
                  iapply HΦ
                  unfold txDone
                  iframe Hdone
                  ileft
                  isplitr
                  · ipureintro; rfl
                  iexact HQ
              · exact absurd rfl Hne
            · -- `writeMeta` failed: log, roll back (only a close if published), return the error
              obtain ⟨ii, rfl⟩ : ∃ ii, err5 = GoInterface.ok ii := by
                cases err5 with
                | nil => exact absurd rfl He5
                | ok ii => exact ⟨ii, rfl⟩
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
                · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe5
                · iempintro
              try wp_auto
              icases Hagr with ⟨%c5, Hagr⟩
              imod ghostVar_update (c5, TxX.wr ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv))) r.n.v _ $$ Hagr with Hagr
              icases Hpost with (⟨Hwl, Hstq, HQ⟩ | ⟨-, Hwl, Hstq, HS, Hau', Hfb⟩)
              · -- published
                have hokF := (cm_pub_ok T.cur Xt wg Xt.v.base (mapLen wg.ms) Pg m' m'' wb'
                  (cmPubPre_congr T.cur Xt wt wg Hgr.1 Hgr.2.1 hpre) hpg
                  (by rw [htxt]; unfold WDb.wtxid; rw [Hgr.1]) Hwgok.1 hms hmapl
                  (by rw [Hgr.1]; exact hflt) Hm' Hm'' Hch.1 Hch.2).2
                have hDn : treeData ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).withC (pubC ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C (Xt.clearPages pml).t.mv Pg)).C = T.cur := hcp.2.2.2.1
                have htx5 : ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv)).t.mv.txid' = W64 ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C.txid + 1 : Nat) : Int) := by
                  show (metaSummed Xt.t.mv).txid' = _
                  rw [metaSummed_txid, htxt]; unfold WDb.wtxid; rw [← Hgr.1]; rfl
                wp_apply wp_rollback K tx r ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv)) ((some Xt.v, some (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C.txid + 1), true, true) : WSt) ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).withC (pubC ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C (Xt.clearPages pml).t.mv Pg))
                  ⟨Xt.v, _, true, true, rfl, htx5,
                    ⟨fun _ => by show wg.ms ≠ none; rw [hms]; simp, fun _ => rfl⟩, fun _ => rfl,
                    fun _ => by show wg.ms ≠ none; rw [hms]; simp⟩
                  $$ [Hw Hwl Hrwl Hcls Hagr Hstq] as Hdone
                · unfold wtxEnd
                  iframe #
                  isplitl [Hw]
                  · ileft; iexact Hw
                  isplitl [Hwl]
                  · simp only [WDb.reslot.proj_C, WDb.reslot.proj_W, WDb.reslot.proj_wb,
                      WDb.reslot.proj_m, WDb.reslot_reslot, WX.clearPages_mv]
                    iexact Hwl
                  iframe Hrwl Hcls
                  isplitl [Hagr]
                  · iexists c5; iexact Hagr
                  isplitl [Hstq]
                  · rw [hDn]; iexact Hstq
                  ipureintro
                  exact ⟨hokF, hwrt, hrlt⟩
                try wp_auto
                wp_bind (App (Val #_) (Val #()))
                iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ err_ptr ↦ _))) $$ [err HtxId Hlgp]
                · iapply Hdf $$ [] err HtxId Hlgp
                  iright; iexact Hfe5
                iintro %vret ⟨%hvret, err⟩
                subst hvret
                wp_auto
                iapply HΦ
                unfold txDone
                iframe Hdone
                iright
                isplitr
                · ipureintro; exact fun h => by cases h
                iframe Hfe5
                ileft
                iexact HQ
              · -- unpublished: the published slots back into W
                icases cm_slots_back K.B K.db K.p K.sp K.t0 tx (wLive Xt.v ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C) (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb) Xt.v.base
                  (mapLen wg.ms) ((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) wb' hms
                  (fun s hs hS => by
                    have hSB := (List.mem_filter.1 hS).1
                    rcases List.mem_append.1 hs with h | h
                    · have h1 := (List.mem_filter.1 h).2
                      have h2 := (List.mem_filter.1 hS).2
                      simp only [h2, Bool.not_true] at h1; exact absurd h1 (by simp)
                    · rcases List.mem_append.1 h with h' | h'
                      · exact ((mem_cmTail _ _ _ s).1 h').2.2.2 hSB
                      · exact ((mem_wMinus _ _ s).1 h').2 (List.mem_append_left _ hSB))
                  (fun s hs => by
                    have := hinSB s (List.mem_filter.1 hs).1
                    exact ⟨this.1, by rw [WDb.reslot.proj_m, Hm''.1]; exact this.2⟩)
                  (fun s hs => Hm'.2.2.2 s (List.mem_append_left _ (List.mem_filter.1 hs).1)
                    (Hch.1 s (List.mem_filter.1 hs).1))
                  $$ [Hwl HS] with Hwl
                · iframe
                have hok3 : wdbOK ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).reslot (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).m (((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) ++ (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).W) (wbUpd ((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) wb' (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).wb)) :=
                  cm_unpub_ok wg m'' (bufSlots Xt.t.bufs) (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) (pubP wg Xt Pg) wb' Hwgok.1 hsub'
                    (by rw [Hm''.1]; exact Hm'.1) (by rw [Hm''.1]; exact hmax) (by rw [Hm''.1]; show m'.size < 2 ^ 63; omega)
                    (by rw [Hm''.2]; exact Hm'.2.2.1)
                    (fun s hs hz => Hm'.2.2.2 s hs (by
                      have := Hm''.1; simp only [WDb.reslot.proj_m] at this; omega))
                    (cm_rest wg _ _ hinW) (by rw [Hgr.1]; exact hflt)
                ihave Hend := cm_wtxEnd_live K tx r ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv)) ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).reslot (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).m (((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) ++ (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).W) (wbUpd ((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) wb' (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).wb)) hwrt hrlt $$ [Hw Hwl Hrwl Hcls Hagr Hstq]
                · iframe #
                  iframe Hw
                  isplitl [Hwl]
                  · iunfold wdbW
                    isplitl
                    · simp only [WDb.reslot.proj_C, WX.withMv_v, WX.clearPages_v]
                      iexact Hwl
                    · ipureintro; exact ⟨hok3, Hwgok.2.1, Hwgok.2.2⟩
                  · unfold cmExcl
                    iframe Hrwl Hcls
                    isplitl [Hagr]
                    · iexists c5; iexact Hagr
                    · simp only [WDb.reslot.proj_C]; iexact Hstq
                have htx6 : ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv)).t.mv.txid' = W64 ((((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).reslot (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).m (((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) ++ (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).W) (wbUpd ((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) wb' (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).wb)).C.txid + 1 : Nat) : Int) := by
                  show (metaSummed Xt.t.mv).txid' = _
                  rw [metaSummed_txid, htxt]; unfold WDb.wtxid; rw [← Hgr.1]; rfl
                wp_apply wp_rollback K tx r ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv)) (wLive ((Xt.clearPages pml).withMv (metaSummed Xt.t.mv)).v ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).reslot (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).m (((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) ++ (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).W) (wbUpd ((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) wb' (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).wb)).C) ((((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).reslot (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).m (((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) ++ (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).W) (wbUpd ((bufSlots Xt.t.bufs).filter (pubP wg Xt Pg)) wb' (((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).reslot m'' ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).W ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).wb).wb))
                  ⟨Xt.v, _, false, true, rfl, htx6,
                    ⟨fun _ => by show wg.ms ≠ none; rw [hms]; simp, fun _ => rfl⟩, fun _ => rfl,
                    fun h => absurd h (by simp)⟩
                  $$ [Hend] as Hdone
                · iexact Hend
                have hC3 : ((wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).reslot (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).m (((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) ++ (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).W) (wbUpd ((bufSlots Xt.t.bufs).filter (fun s => !pubP wg Xt Pg s)) wb' (wg.reslot m' ((cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ (wMinus wg.W ((bufSlots Xt.t.bufs) ++ (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))))) (wbUpd (cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).wb)).C = wt.C := by
                  simp only [WDb.reslot.proj_C]; exact Hgr.1
                ihave Hau'' : commitAU K γ.ns (treeData wt.C) T.cur Q $$ [Hau']
                · first | iexact Hau' | (rw [← Hgr.1]; iexact Hau') | (rw [← hC3]; iexact Hau')
                ihave Hau : AU <{ ∃∃ (D' : Data), boltState γ 1 D' }> @ ⊤ \ ↑γ.ns, ∅
                    <{ ⌜D' = T.base⌝ ∗ boltState γ 1 T.cur, COMM Q }> $$ [Hau'']
                · unfold commitAU
                  rw [hbt]
                  unfold boltState
                  rw [hB]
                  iexact Hau''
                irename Hfe5 => Hfe1
                cm_return
          · -- `write` failed: log, roll back, return the error
            obtain ⟨ii, rfl⟩ : ∃ ii, err4 = GoInterface.ok ii := by
              cases err4 with
              | nil => exact absurd rfl He4
              | ok ii => exact ⟨ii, rfl⟩
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
              · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe4
              · iempintro
            try wp_auto
            have hok4 := wdbOK_written wg m' _ wb' Hwgok.1 hsub' Hm'.1 hmax (by omega) Hm'.2.2.1
              Hm'.2.2.2 (cm_rest wg _ _ hinW) (by rw [Hgr.1]; exact hflt)
            imod cm_excl_update K r Xt (Xt.clearPages pml) _ $$ Hex with Hex
            ihave Hend := cm_wtxEnd_live K tx r (Xt.clearPages pml)
              (wg.reslot m' ((bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ wMinus wg.W (bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))) (wbUpd (bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)) hwrt hrlt
              $$ [Hw Hwl Hex]
            · iframe; iframe #
              isplitl [Hwl]
              · iunfold wdbW
                isplitl
                · rw [WX.clearPages_v, WDb.reslot.proj_C]; iexact Hwl
                · ipureintro; exact ⟨hok4, Hwgok.2.1, Hwgok.2.2⟩
              · rw [WDb.reslot.proj_C, Hgr.1]; iexact Hex
            have htxg : (Xt.clearPages pml).t.mv.txid' =
                W64 (((wg.reslot m' ((bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ wMinus wg.W (bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))) (wbUpd (bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).C.txid + 1 : Nat) : Int) := by
              rw [WX.clearPages_mv, htxt, WDb.reslot.proj_C, Hgr.1]; rfl
            wp_apply wp_rollback K tx r (Xt.clearPages pml) (wLive (Xt.clearPages pml).v (wg.reslot m' ((bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ wMinus wg.W (bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))) (wbUpd (bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb)).C)
              (wg.reslot m' ((bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) ++ wMinus wg.W (bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms))) (wbUpd (bufSlots Xt.t.bufs ++ cmTail wg (bufSlots Xt.t.bufs) (mapLen wg.ms)) wb' wg.wb))
              ⟨Xt.v, _, false, true, rfl, htxg,
                ⟨fun _ => by rw [WDb.reslot.proj_ms, hms]; simp, fun _ => rfl⟩, fun _ => rfl,
                fun h => absurd h (by simp)⟩
              $$ [Hend] as Hdone
            · iexact Hend
            irename Hfe4 => Hfe1
            cm_return
        · subst hv
          cases e1 with
          | nil => exact absurd rfl He1
          | ok ii =>
          try wp_auto
          cm_return
      · subst hv
        cases e1 with
        | nil => exact absurd rfl He1
        | ok ii =>
        try wp_auto
        cm_return
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
