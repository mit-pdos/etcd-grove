/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ordering/txnOrdering__Commit.lean`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ordering.txnOrdering__Commit
public import Spec.go_etcd_io.etcd.client.v3.ordering.kvOrdering__getPrevRev
public import Spec.go_etcd_io.etcd.client.v3.ordering.kvOrdering__setPrevRev
public import Spec.go_etcd_io.etcd.client.v3.ordering.isReadOnly
public import Spec.go_etcd_io.etcd.client.v3.OpTxn
public import Spec.go_etcd_io.etcd.client.v3.OpResponse__Txn

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.ordering go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

theorem txnOrdering.Commit.wp_proof
    (hGetPrev : kvOrdering.getPrevRev.spec (GF := GF) (hG := hG))
    (hSetPrev : kvOrdering.setPrevRev.spec (GF := GF) (hG := hG))
    (hOpTxn : EtcdGrove.OpTxn.spec (GF := GF) (hG := hG))
    (hIsReadOnly : isReadOnly.spec (GF := GF) (hG := hG))
    (hRespTxn : EtcdGrove.OpResponse.Txn.spec (GF := GF) (hG := hG)) :
    txnOrdering.Commit.spec (GF := GF) (hG := hG) := by
  intro txnp kvp innerTxn kv vf ctx st R P PostOk PostErr
  wp_start as ⟨#Hkv, Htxn, Hrw, HP_cond, #Hdo, #Hvf⟩
  iunfold isKvOrdering at Hkv
  icases Hkv with ⟨%Hkvp, #HKV, #Hvf_fld⟩
  iunfold ownTxnOrdering at Htxn
  icases Htxn with ⟨%Htxnp, #HTxn_fld, #Hkvp_fld, #Hctx_fld, #Hmu, Hcmps_fld, #Hcmps, Hthen_fld, #Hts, Helse_fld, #Hes⟩
  iunfold kvDoTxnSpec at Hdo
  iunfold orderViolationSpec at Hvf
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  wp_method_call
  wp_auto
  wp_apply (hGetPrev kvp R) $$ [$Hrw] as %prevRev ⟨Hrw, #HRprev⟩
  (try wp_auto)
  wp_apply (hOpTxn st.csl st.ms st.tsl st.esl) $$ [$Hcmps] as %opv ⟨#Hfull, #Hcmps', %Hte⟩
  ihave #HopTxn := opTAtC_of_OpTxn opv st.ms st.tsl st.esl st.ts st.es Hte.1 Hte.2 $$ [$Hfull $Hcmps' $Hts $Hes]
  (try wp_auto)
  wp_apply (hIsReadOnly opv (.txn OpFull.txnInit st.ms st.ts st.es)) $$ [$HopTxn]
  (try wp_auto)
  cases hro : isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es)
  · -- Case 1: `isReadOnlyM = false` (mutable transaction: `HP_cond` is linear `P`, executed at most once)
    simp only [Bool.false_eq_true, ↓reduceIte]
    ihave IH : iprop(
        "txn" ∷ txn_ptr ↦ txnp ∗
        "prevRev" ∷ prevRev_ptr ↦ prevRev ∗
        "opTxn" ∷ opTxn_ptr ↦ opv ∗
        "canRetry" ∷ canRetry_ptr ↦ false ∗
        "Hcmps_fld" ∷ structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"cmps" txnp ↦ st.csl ∗
        "Hthen_fld" ∷ structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"thenOps" txnp ↦ st.tsl ∗
        "Helse_fld" ∷ structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"elseOps" txnp ↦ st.esl ∗
        "Hrw" ∷ kvOrderingHandle kvp R ∗
        "HP" ∷ P)
      $$ [txn prevRev opTxn canRetry Hcmps_fld Hthen_fld Helse_fld Hrw HP_cond]
    · simp only [named]; iframe
    wp_for IH
    (try wp_auto)
    wp_apply Hdo $$ %opv [$HP $HopTxn] as %opResp %err Herr
    cases err with
    | nil =>
      simp only [_root_.decide_true, ↓reduceIte]
      icases Herr with ⟨%hdr, %rev, ⟨%Hr_nn, %Hhdr_nn⟩, #Hhdr, #Hrev, #HRrev, Hok⟩
      wp_auto
      wp_apply (hRespTxn opResp_ptr opResp (DFrac.own 1)) $$ [$opResp] as opResp
      (try wp_auto)
      wp_if_destruct
      · -- `rev ≥ prevRev`
        (try wp_auto)
        wp_method_call
        wp_auto
        wp_apply (hSetPrev kvp rev R) $$ [$Hrw $HRrev] as Hrw
        (try wp_auto)
        wp_for_post
        iapply HΦ
        simp only [_root_.decide_true, ↓reduceIte]
        iunfold ownTxnOrdering
        iframe Hcmps_fld Hthen_fld Helse_fld Hrw
        isplitl []
        · iframe #; ipureintro; exact Htxnp
        iexists prevRev, rev, hdr
        iframe #
        iframe Hok
        ipureintro; refine ⟨Hr_nn, Hhdr_nn, fun h => by simp [hro] at h⟩
      · -- `rev < prevRev`: call `orderViolationFunc`, then `!canRetry` is `true` so returns immediately!
        (try wp_auto)
        wp_apply Hvf $$ %opv %opResp %prevRev [$HRprev] as %err2 Herr2
        cases err2 with
        | nil =>
          simp only [_root_.decide_true, Bool.not_false, ↓reduceIte]
          (try wp_auto)
          wp_for_post
          iapply HΦ
          simp only [_root_.decide_true, ↓reduceIte]
          iunfold ownTxnOrdering
          iframe Hcmps_fld Hthen_fld Helse_fld Hrw
          isplitl []
          · iframe #; ipureintro; exact Htxnp
          iexists prevRev, rev, hdr
          iframe #
          iframe Hok
          ipureintro; refine ⟨Hr_nn, Hhdr_nn, fun h => by simp [hro] at h⟩
        | ok ei2 =>
          have herr2 : GoInterface.ok ei2 ≠ GoInterface.nil := by simp
          simp only [decide_eq_false herr2, Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          wp_for_post
          iapply HΦ
          simp only [decide_eq_false herr2, Bool.false_eq_true, ↓reduceIte]
          iunfold ownTxnOrdering
          iframe Hcmps_fld Hthen_fld Helse_fld Hrw Herr2
          iframe #
          ipureintro; exact Htxnp
    | ok ei =>
      have herr : GoInterface.ok ei ≠ GoInterface.nil := by simp
      simp only [decide_eq_false herr, Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      wp_for_post
      iapply HΦ
      simp only [decide_eq_false herr, Bool.false_eq_true, ↓reduceIte]
      iunfold ownTxnOrdering
      iframe Hcmps_fld Hthen_fld Helse_fld Hrw Herr
      iframe #
      ipureintro; exact Htxnp
  · -- Case 2: `isReadOnlyM = true` (read-only transaction: `HP_cond` is persistent `□ P`, retries until `rev ≥ prevRev`)
    simp only [↓reduceIte]
    icases HP_cond with #HP
    ihave IH : iprop(
        "txn" ∷ txn_ptr ↦ txnp ∗
        "prevRev" ∷ prevRev_ptr ↦ prevRev ∗
        "opTxn" ∷ opTxn_ptr ↦ opv ∗
        "canRetry" ∷ canRetry_ptr ↦ true ∗
        "Hcmps_fld" ∷ structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"cmps" txnp ↦ st.csl ∗
        "Hthen_fld" ∷ structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"thenOps" txnp ↦ st.tsl ∗
        "Helse_fld" ∷ structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"elseOps" txnp ↦ st.esl ∗
        "Hrw" ∷ kvOrderingHandle kvp R)
      $$ [txn prevRev opTxn canRetry Hcmps_fld Hthen_fld Helse_fld Hrw]
    · simp only [named]; iframe
    wp_for IH
    (try wp_auto)
    wp_apply Hdo $$ %opv [$HP $HopTxn] as %opResp %err Herr
    cases err with
    | nil =>
      simp only [_root_.decide_true, ↓reduceIte]
      icases Herr with ⟨%hdr, %rev, ⟨%Hr_nn, %Hhdr_nn⟩, #Hhdr, #Hrev, #HRrev, Hok⟩
      wp_auto
      wp_apply (hRespTxn opResp_ptr opResp (DFrac.own 1)) $$ [$opResp] as opResp
      (try wp_auto)
      wp_if_destruct
      · -- `rev ≥ prevRev`
        (try wp_auto)
        wp_method_call
        wp_auto
        wp_apply (hSetPrev kvp rev R) $$ [$Hrw $HRrev] as Hrw
        (try wp_auto)
        wp_for_post
        iapply HΦ
        simp only [_root_.decide_true, ↓reduceIte]
        iunfold ownTxnOrdering
        iframe Hcmps_fld Hthen_fld Helse_fld Hrw
        isplitl []
        · iframe #; ipureintro; exact Htxnp
        iexists prevRev, rev, hdr
        iframe #
        iframe Hok
        ipureintro; refine ⟨Hr_nn, Hhdr_nn, fun _ => Hif⟩
      · -- `rev < prevRev`: call `orderViolationFunc`, and if `nil`, continue loop!
        (try wp_auto)
        wp_apply Hvf $$ %opv %opResp %prevRev [$HRprev] as %err2 Herr2
        cases err2 with
        | nil =>
          simp only [_root_.decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          wp_for_post
          simp only [named]; iframe
        | ok ei2 =>
          have herr2 : GoInterface.ok ei2 ≠ GoInterface.nil := by simp
          simp only [decide_eq_false herr2, Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          wp_for_post
          iapply HΦ
          simp only [decide_eq_false herr2, Bool.false_eq_true, ↓reduceIte]
          iunfold ownTxnOrdering
          iframe Hcmps_fld Hthen_fld Helse_fld Hrw Herr2
          iframe #
          ipureintro; exact Htxnp
    | ok ei =>
      have herr : GoInterface.ok ei ≠ GoInterface.nil := by simp
      simp only [decide_eq_false herr, Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      wp_for_post
      iapply HΦ
      simp only [decide_eq_false herr, Bool.false_eq_true, ↓reduceIte]
      iunfold ownTxnOrdering
      iframe Hcmps_fld Hthen_fld Helse_fld Hrw Herr
      iframe #
      ipureintro; exact Htxnp

end proof

end ordering
end EtcdGrove
end Perennial
