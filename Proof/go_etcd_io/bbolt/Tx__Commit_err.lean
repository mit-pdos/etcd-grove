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
        WP (App (Val #f) (Val #())) {{ _v, err_ptr ↦ e }})))) $$ [txId lg defer]
  · cases bl
    · wp_auto
      iframe
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %e - Herr - -
      wp_auto
      iexact Herr
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
      · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
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
        · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
          isplitl
          · iapply logArgOk_int
          · iempintro
        try wp_auto
        iexact Herr
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
          · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
            isplitl
            · iapply logArgOk_int
            · iempintro
          try wp_auto
          iexact Herr
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
          · try simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
            isplitl
            · iapply logArgOk_of_fmtErrorOk _ _ (by simp [methodVerbs]) (GoInterface.ok ii) $$ Hfe
            · iempintro
          try wp_auto
          iexact Herr
  trace_state
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
