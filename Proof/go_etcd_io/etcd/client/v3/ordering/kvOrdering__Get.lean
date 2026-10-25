/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ordering/kvOrdering__Get.lean`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ordering.kvOrdering__Get
public import Spec.go_etcd_io.etcd.client.v3.ordering.kvOrdering__getPrevRev
public import Spec.go_etcd_io.etcd.client.v3.ordering.kvOrdering__setPrevRev
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.OpResponse__Get

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

theorem kvOrdering.Get.wp_proof
    (hGetPrev : kvOrdering.getPrevRev.spec (GF := GF) (hG := hG))
    (hSetPrev : kvOrdering.setPrevRev.spec (GF := GF) (hG := hG))
    (hOpGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hRespGet : EtcdGrove.OpResponse.Get.spec (GF := GF) (hG := hG)) :
    kvOrdering.Get.spec (GF := GF) (hG := hG) := by
  intro kvp kv vf ctx key sl gs R PostOk PostErr
  wp_start as ⟨#Hkv, Hrw, Hopts, %Hnopanic, #Hdo, #Hvf⟩
  iunfold isKvOrdering at Hkv
  icases Hkv with ⟨%Hkvp, #HKV, #Hvf_fld⟩
  iunfold kvDoGetSpec at Hdo
  iunfold orderViolationSpec at Hvf
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply (hGetPrev kvp R) $$ [$Hrw] as %prevRev ⟨Hrw, #HRprev⟩
  (try wp_auto)
  wp_apply (hOpGet key sl gs) $$ [$Hopts] as %opv #Hop
  · ipureintro; exact Hnopanic
  (try wp_auto)
  ihave IH : iprop(
      "kv" ∷ kv_ptr ↦ kvp ∗
      "ctx" ∷ ctx_ptr ↦ ctx ∗
      "prevRev" ∷ prevRev_ptr ↦ prevRev ∗
      "op" ∷ op_ptr ↦ opv ∗
      "Hrw" ∷ kvOrderingHandle kvp R) $$ [kv ctx prevRev op Hrw]
  · simp only [named]; iframe
  wp_for IH
  (try wp_auto)
  wp_apply Hdo $$ %opv [$Hop] as %r %err Herr
  cases err with
  | nil =>
    simp only [_root_.decide_true, ↓reduceIte]
    icases Herr with ⟨%hdr, %rev, ⟨%Hr_nn, %Hhdr_nn⟩, #Hhdr, #Hrev, #HRrev, Hok⟩
    wp_auto
    wp_apply (hRespGet r_ptr r (DFrac.own 1)) $$ [$r] as r
    (try wp_auto)
    wp_if_destruct
    · -- `rev = prevRev`
      (try wp_auto)
      wp_for_post
      iapply HΦ
      simp only [_root_.decide_true, ↓reduceIte]
      iframe Hrw
      iexists prevRev, rev, hdr
      iframe #
      iframe Hok
      ipureintro; refine ⟨Hr_nn, Hhdr_nn, by subst Hif; omega⟩
    · wp_if_destruct
      · -- `rev > prevRev`
        (try wp_auto)
        wp_apply (hSetPrev kvp rev R) $$ [$Hrw $HRrev] as Hrw
        (try wp_auto)
        wp_for_post
        iapply HΦ
        simp only [_root_.decide_true, ↓reduceIte]
        iframe Hrw
        iexists prevRev, rev, hdr
        iframe #
        iframe Hok
        ipureintro; refine ⟨Hr_nn, Hhdr_nn, by omega⟩
      · -- `rev < prevRev`: call `orderViolationFunc(op, r, prevRev)`
        (try wp_auto)
        wp_apply Hvf $$ %opv %r %prevRev [$HRprev] as %err2 Herr2
        cases err2 with
        | nil =>
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
          iframe
  | ok ei =>
    have herr : GoInterface.ok ei ≠ GoInterface.nil := by simp
    simp only [decide_eq_false herr, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    wp_for_post
    iapply HΦ
    simp only [decide_eq_false herr, Bool.false_eq_true, ↓reduceIte]
    iframe

end proof

end ordering
end EtcdGrove
end Perennial
