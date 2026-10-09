/-
Proof of `Spec/Cache__validateWatch.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__validateWatch
public import Spec.go_etcd_io.etcd.client.v3.Op__IsPrevKV
public import Spec.go_etcd_io.etcd.client.v3.Op__IsFragment
public import Spec.go_etcd_io.etcd.client.v3.Op__IsCreatedNotify
public import Spec.go_etcd_io.etcd.client.v3.Op__IsFilterPut
public import Spec.go_etcd_io.etcd.client.v3.Op__IsFilterDelete
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.cache.v3.Cache__validateRange
public import Spec.go_etcd_io.etcd.cache.v3.KeyPredForRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.validateWatch.wp_proof
    (wp_IsPrevKV : Op.IsPrevKV.spec (GF := GF) (hG := hG))
    (wp_IsFragment : Op.IsFragment.spec (GF := GF) (hG := hG))
    (wp_IsCreatedNotify : Op.IsCreatedNotify.spec (GF := GF) (hG := hG))
    (wp_IsFilterPut : Op.IsFilterPut.spec (GF := GF) (hG := hG))
    (wp_IsFilterDelete : Op.IsFilterDelete.spec (GF := GF) (hG := hG))
    (wp_RangeBytes : Op.RangeBytes.spec (GF := GF) (hG := hG))
    (wp_validateRange : Cache.validateRange.spec (GF := GF) (hG := hG))
    (wp_KeyPredForRange : KeyPredForRange.spec (GF := GF) (hG := hG)) :
    Cache.validateWatch.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap key op o
  wp_start as ⟨#Hc, #Ho⟩
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, ⟨%eUR, #HeUR⟩, ⟨%eKR, #HeKR⟩⟩
  ihave #Hcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_IsPrevKV $$ [$op $Ho] as op
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e _
    iapply HΦ
    have hu : o.watchUnsupported = true := by simp [OpModel.watchUnsupported, ← Hif]
    simp only [validateResult, hu, ↓reduceIte]
    ipureintro; simp
  have HprevKV : o.prevKV = false := by simpa using Hif
  wp_apply wp_IsFragment $$ [$op $Ho] as op
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e _
    iapply HΦ
    have hu : o.watchUnsupported = true := by simp [OpModel.watchUnsupported, ← Hif]
    simp only [validateResult, hu, ↓reduceIte]
    ipureintro; simp
  have Hfragment : o.fragment = false := by simpa using Hif
  wp_apply wp_IsCreatedNotify $$ [$op $Ho] as op
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e _
    iapply HΦ
    have hu : o.watchUnsupported = true := by simp [OpModel.watchUnsupported, ← Hif]
    simp only [validateResult, hu, ↓reduceIte]
    ipureintro; simp
  have HcreatedNotify : o.createdNotify = false := by simpa using Hif
  wp_apply wp_IsFilterPut $$ [$op $Ho] as op
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e _
    iapply HΦ
    have hu : o.watchUnsupported = true := by simp [OpModel.watchUnsupported, ← Hif]
    simp only [validateResult, hu, ↓reduceIte]
    ipureintro; simp
  have HfilterPut : o.filterPut = false := by simpa using Hif
  wp_apply wp_IsFilterDelete $$ [$op $Ho] as op
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e _
    iapply HΦ
    have hu : o.watchUnsupported = true := by simp [OpModel.watchUnsupported, ← Hif]
    simp only [validateResult, hu, ↓reduceIte]
    ipureintro; simp
  have HfilterDelete : o.filterDelete = false := by simpa using Hif
  have hu : o.watchUnsupported = false := by simp [OpModel.watchUnsupported, HprevKV, Hfragment, HcreatedNotify, HfilterPut, HfilterDelete]
  wp_apply wp_string_to_bytes key as %ssl ⟨Hssl, -⟩
  ipersist Hssl
  wp_apply wp_RangeBytes $$ [$op $Ho] as %esl ⟨op, #Hesl⟩
  wp_apply wp_validateRange c cf γr γd cap ssl esl key o.rangeEnd DFrac.discard DFrac.discard $$ [$Hc $Hssl $Hesl] as %err ⟨-, -, #Herr⟩
  cases hv : validRange cf.pfx key o.rangeEnd
  · simp only [rangeErr, hv, Bool.false_eq_true, ↓reduceIte]
    icombine HeKR Herr gives %Heq
    subst Heq
    wp_auto
    iapply HΦ
    simp only [validateResult, hu, hv, Bool.false_eq_true, ↓reduceIte]
    isplitr
    · ipureintro; trivial
    · iexact HeKR
  · simp only [rangeErr, hv, ↓reduceIte]
    icases Herr with %Herr
    subst Herr
    wp_auto
    wp_apply wp_KeyPredForRange ssl esl key o.rangeEnd $$ [$Hssl $Hesl] as %f ⟨%Hf, #Hspec⟩
    iapply HΦ
    simp only [validateResult, hu, hv, Bool.false_eq_true, ↓reduceIte]
    isplitr
    · ipureintro; exact ⟨trivial, Hf⟩
    · iexact Hspec

end proof

end EtcdGrove
end Perennial
