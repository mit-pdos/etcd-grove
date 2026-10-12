/-
Proof of `Spec/Cache__validateGet.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__validateGet
public import Spec.go_etcd_io.etcd.client.v3.Op__IsCountOnly
public import Spec.go_etcd_io.etcd.client.v3.Op__IsPrevKV
public import Spec.go_etcd_io.etcd.client.v3.Op__IsSortSet
public import Spec.go_etcd_io.etcd.client.v3.Op__Limit
public import Spec.go_etcd_io.etcd.client.v3.Op__MinModRev
public import Spec.go_etcd_io.etcd.client.v3.Op__MaxModRev
public import Spec.go_etcd_io.etcd.client.v3.Op__MinCreateRev
public import Spec.go_etcd_io.etcd.client.v3.Op__MaxCreateRev
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.validateGet.wp_proof
    (wp_IsCountOnly : Op.IsCountOnly.spec (GF := GF) (hG := hG))
    (wp_IsPrevKV : Op.IsPrevKV.spec (GF := GF) (hG := hG))
    (wp_IsSortSet : Op.IsSortSet.spec (GF := GF) (hG := hG))
    (wp_Limit : Op.Limit.spec (GF := GF) (hG := hG))
    (wp_MinModRev : Op.MinModRev.spec (GF := GF) (hG := hG))
    (wp_MaxModRev : Op.MaxModRev.spec (GF := GF) (hG := hG))
    (wp_MinCreateRev : Op.MinCreateRev.spec (GF := GF) (hG := hG))
    (wp_MaxCreateRev : Op.MaxCreateRev.spec (GF := GF) (hG := hG))
    (wp_RangeBytes : Op.RangeBytes.spec (GF := GF) (hG := hG))
    (wp_validateRange : Cache.validateRange.spec (GF := GF) (hG := hG))
    (wp_KeyPredForRange : KeyPredForRange.spec (GF := GF) (hG := hG)) :
    Cache.validateGet.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap key op o
  wp_start as ⟨#Hc, #Ho⟩
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, ⟨%eUR, #HeUR⟩, ⟨%eKR, #HeKR⟩, -⟩
  ihave #Hcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_IsCountOnly $$ [$Ho]
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e #HeS
    iapply HΦ
    have hu : o.getUnsupported = true := by simp [OpModel.getUnsupported, ← Hif]
    simp only [validateResult, hu, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iexists e
    isplitr
    · ipureintro; simp
    unfold errorStringSpec; iexact HeS
  have HcountOnly : o.countOnly = false := by simpa using Hif
  wp_apply wp_IsPrevKV $$ [$Ho]
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e #HeS
    iapply HΦ
    have hu : o.getUnsupported = true := by simp [OpModel.getUnsupported, ← Hif]
    simp only [validateResult, hu, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iexists e
    isplitr
    · ipureintro; simp
    unfold errorStringSpec; iexact HeS
  have HprevKV : o.prevKV = false := by simpa using Hif
  wp_apply wp_IsSortSet $$ [$Ho]
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e #HeS
    iapply HΦ
    have hu : o.getUnsupported = true := by simp [OpModel.getUnsupported, ← Hif]
    simp only [validateResult, hu, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iexists e
    isplitr
    · ipureintro; simp
    unfold errorStringSpec; iexact HeS
  have HsortSet : o.sortSet = false := by simpa using Hif
  wp_apply wp_Limit $$ [$Ho]
  wp_if_destruct
  · wp_apply wp_Limit $$ [$Ho]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e #HeS
    iapply HΦ
    have hne : o.limit ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
    have hu : o.getUnsupported = true := by
      rw [OpModel.getUnsupported, decide_eq_true_eq]; right; right; right; left; exact hne
    simp only [validateResult, hu, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iexists e
    isplitr
    · ipureintro; simp
    unfold errorStringSpec; iexact HeS
  have Hlimit : o.limit = W64 0 := Classical.byContradiction fun hne => Hif (by rw [decide_eq_false hne]; rfl)
  wp_apply wp_MinModRev $$ [$Ho]
  wp_if_destruct
  · wp_apply wp_MinModRev $$ [$Ho]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e #HeS
    iapply HΦ
    have hne : o.minModRev ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
    have hu : o.getUnsupported = true := by
      rw [OpModel.getUnsupported, decide_eq_true_eq]; right; right; right; right; left; exact hne
    simp only [validateResult, hu, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iexists e
    isplitr
    · ipureintro; simp
    unfold errorStringSpec; iexact HeS
  have HminModRev : o.minModRev = W64 0 := Classical.byContradiction fun hne => Hif (by rw [decide_eq_false hne]; rfl)
  wp_apply wp_MaxModRev $$ [$Ho]
  wp_if_destruct
  · wp_apply wp_MaxModRev $$ [$Ho]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e #HeS
    iapply HΦ
    have hne : o.maxModRev ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
    have hu : o.getUnsupported = true := by
      rw [OpModel.getUnsupported, decide_eq_true_eq]; right; right; right; right; right; left; exact hne
    simp only [validateResult, hu, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iexists e
    isplitr
    · ipureintro; simp
    unfold errorStringSpec; iexact HeS
  have HmaxModRev : o.maxModRev = W64 0 := Classical.byContradiction fun hne => Hif (by rw [decide_eq_false hne]; rfl)
  wp_apply wp_MinCreateRev $$ [$Ho]
  wp_if_destruct
  · wp_apply wp_MinCreateRev $$ [$Ho]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e #HeS
    iapply HΦ
    have hne : o.minCreateRev ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
    have hu : o.getUnsupported = true := by
      rw [OpModel.getUnsupported, decide_eq_true_eq]; right; right; right; right; right; right; left; exact hne
    simp only [validateResult, hu, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iexists e
    isplitr
    · ipureintro; simp
    unfold errorStringSpec; iexact HeS
  have HminCreateRev : o.minCreateRev = W64 0 := Classical.byContradiction fun hne => Hif (by rw [decide_eq_false hne]; rfl)
  wp_apply wp_MaxCreateRev $$ [$Ho]
  wp_if_destruct
  · wp_apply wp_MaxCreateRev $$ [$Ho]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e #HeS
    iapply HΦ
    have hne : o.maxCreateRev ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
    have hu : o.getUnsupported = true := by
      rw [OpModel.getUnsupported, decide_eq_true_eq]; right; right; right; right; right; right; right; exact hne
    simp only [validateResult, hu, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iexists e
    isplitr
    · ipureintro; simp
    unfold errorStringSpec; iexact HeS
  have HmaxCreateRev : o.maxCreateRev = W64 0 := Classical.byContradiction fun hne => Hif (by rw [decide_eq_false hne]; rfl)
  have hu : o.getUnsupported = false := by simp [OpModel.getUnsupported, HcountOnly, HprevKV, HsortSet, Hlimit, HminModRev, HmaxModRev, HminCreateRev, HmaxCreateRev]
  wp_apply wp_string_to_bytes key as %ssl ⟨Hssl, -⟩
  ipersist Hssl
  wp_apply wp_RangeBytes $$ [$Ho] as %esl #Hesl
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
