/-
Proof of `Spec/Cache__getWatch.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatch
public import Spec.go_etcd_io.etcd.cache.v3.Cache__get
public import Spec.go_etcd_io.etcd.cache.v3.Cache__watch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.getWatch.wp_proof
    (wp_get : Cache.get.spec (GF := GF) (hG := hG))
    (wp_watch : Cache.watch.spec (GF := GF) (hG := hG)) :
    Cache.getWatch.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap c0
  wp_start as ⟨#Hc, Hw, Hrun⟩
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  icases HisICtx with ⟨%ics, #Hctxi, -⟩
  unfold cacheWriter
  icases Hw with ⟨Hdw, #Hwo, %B, Hbd⟩
  wp_auto
  wp_apply wp_get c cf γr γd cap cf.ictx ics B $$ [$Hpkg $Hc $Hctxi $Hbd] as %resp %err Hres
  icases Hres with (⟨%Herr, Hbd, #HeS⟩ | ⟨%Herr, %R, #Hrev, Hbd, #Hlb, #Hslb, %HRb⟩)
  · -- the get failed: return its error
    obtain ⟨-, Hne⟩ := Herr
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; intro h; cases h
    iframe HeS
    iframe Hrun
    iexists c0
    iframe Hdw
    isplitr
    · iexact Hwo
    iexists B; iexact Hbd
  subst Herr
  iunfold getRespRev at Hrev
  icases Hrev with ⟨%hdr, #Hh, %Hnn, #Hr⟩
  wp_auto
  iunfold cacheBound at Hbd
  icases Hbd with ⟨Ha, #HeR, %HR0⟩
  have hR1 : sint.Z (R + W64 1) = sint.Z R + 1 := by
    have := HRb.2; word
  wp_apply wp_watch c cf γr γd cap (R + W64 1) R c0 $$ [$Hpkg $Hc Hdw Ha Hrun $Hslb]
    as %err ⟨%Hne, #HeS, Hrun, %c1, Hw⟩
  · unfold cacheWriter
    iframe Hdw Hrun
    isplitl
    · isplitr
      · iexact Hwo
      iexists R
      unfold cacheBound
      iframe Ha HeR
      ipureintro; exact HR0
    ipureintro; omega
  iapply HΦ
  isplitr
  · ipureintro; exact Hne
  iframe HeS
  iframe Hrun
  iexists c1
  iunfold cacheWriter at Hw
  iexact Hw

end proof

end EtcdGrove
end Perennial
