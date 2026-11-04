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
public import Proof.go_etcd_io.bbolt.DB__Begin_err
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
public import Proof.go_etcd_io.bbolt.Commit.AssembleGaps
public import Proof.go_etcd_io.bbolt.Commit.AssembleAcc
public import Proof.go_etcd_io.bbolt.Commit.AssemblePure
public import Proof.go_etcd_io.bbolt.Commit.AssembleEnd
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX
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
  icases Hg with ⟨%w, %extra, Hwdb, Hshape, %Hflv⟩
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
  wp_apply wp_logger_ne_discard lg Hlgty $$ [] as %bl -
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
  icases cm_keep_pure (wtx_wMetaOK K tx r false X w) $$ [Hw Hwdb] with ⟨⟨Hw, Hwdb⟩, %Hmeta⟩
  · iframe
  icases (cm_keep_pure (cm_wdbW_ok K tx X.v w)) $$ Hwdb
    with ⟨Hwdb, %Hwok⟩
  have hbase : T.base = treeData w.C := by
    rw [Hf.2.2.1]
    have e : X.v.data = (View.ofC X.v.base w.C).data := congrArg View.data Hwok.2.2
    rw [e]; rfl
  ihave Hex : cmExcl K r X (treeData w.C) $$ [Hrwl Hcls Hshape Hv Hst]
  · unfold cmExcl; rw [← hbase]
    iframe
  have hvwf : viewWF X.v := Hf.1.2.2.2.2.2.2.2
  have hld : ∀ bl, X.t.bs !! bl ≠ none → leafDepthOK X bl := fun bl hb =>
    leafDepthOK_rt X bl (rtOK_init X bl Hf.1 hvwf (Option.isSome_iff_ne_none.2 hb))
  wp_apply wp_rebalance K tx r false X w Hf.1 hld (wOK_liveReach X Hf.1) Hflv $$ [Hw Hwdb]
    as ⟨%X1, %fl1, Hw, Hwdb, %Hrb⟩
  · iframe
  imod cm_excl_update K r X X1 _ (fun e => txShape_rebalOK r.n.pg X X1 w.fl fl1 _ e Hrb.1) $$ Hex
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
  obtain ⟨hrbOK, hreach1, hflv1⟩ := Hrb
  have hv1 : X1.v = X.v := hrbOK.2.2.1
  have hmv1 : X1.t.mv = X.t.mv := sorry -- Gap 6: `rebalance`'s post should say the meta copy is unchanged
  rw [← hv1]
  have hmap1 : X1.t.mv.pgid'.toNat * 4096 ≤ mapLen (w.withFl fl1).ms := by
    rw [hmv1, show (w.withFl fl1).ms = w.ms from rfl, Hmeta.2.2.2.1]
    exact Hwok.1.2.2.2.2.2.2.2.2.1 _ _ Hwok.2.1
  wp_apply wp_spill K tx r false X1 (w.withFl fl1) (spillPre_of_rebalOK X X1 w.fl fl1 _ hrbOK)
    hreach1 hmap1 hflv1 $$ [Hw Hwdb] as %err1 Hsp
  · iframe
  cases lg with
  | nil => iexfalso; unfold dbLogger boltLogger; iexact Hlgok
  | ok li =>
  ihave #Hlgok' : boltLogger (GF := GF) (.ok li) $$ []
  · unfold dbLogger; iexact Hlgok
  icases Hsp with (⟨%He1, %X2, %w2, Hw, Hwdb, %Hsp⟩ | ⟨%He1, #Hfe1, %X2, %w2, %st, %Hsp, Hres⟩)
  · -- spilled
    subst He1
    obtain ⟨hspOK, hC2, hderef2, hfresh2, hreach2, hmap2, hflv2, hbufs2⟩ := Hsp
    try wp_auto
    wp_apply time.wp_Since as %d -
    try wp_auto
    icases cm_stats_acc K tx r false X2 $$ Hw with ⟨-, -, Hst2, Hwb⟩
    wp_apply wp_IncSpillTime K tx r false 1 $$ [Hst2] as %_ Hst2
    · iframe; iframe #
    ihave Hw := Hwb $$ Hst2
    try wp_auto
    sorry
  · -- `spill` failed: log, roll back, return the error
    obtain ⟨ii, rfl⟩ : ∃ ii, err1 = GoInterface.ok ii := by
      cases err1 with
      | nil => exact absurd rfl He1
      | ok ii => exact ⟨ii, rfl⟩
    obtain ⟨hC2, -, -⟩ := Hsp
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
    have hwr2 : X2.t.t.writable' = true := sorry
    have hrl2 : (X2.t.bs !! X2.rl).isSome := sorry
    have htx2 : X2.t.mv.txid' = W64 ((w2.C.txid + 1 : Nat) : Int) := sorry
    imod cm_excl_update K r X1 X2 _ (by intro e; sorry) $$ Hex with Hex
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
