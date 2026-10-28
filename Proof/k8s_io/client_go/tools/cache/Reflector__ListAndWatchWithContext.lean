/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__ListAndWatchWithContext.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__ListAndWatchWithContext
public import Spec.k8s_io.client_go.tools.cache.Reflector__watchWithResync
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.github_com.go_logr.logr.Logger__V_ptr
public import Spec.github_com.go_logr.logr.Logger__Info

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache apimodel informer

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem Reflector.ListAndWatchWithContext.wp_proof
    (wp_list : Reflector.list.spec (GF := GF) (hG := hG))
    (wp_watchWithResync : Reflector.watchWithResync.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_V_ptr : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG)) :
    Reflector.ListAndWatchWithContext.spec (GF := GF) (hG := hG) := by
  intro r f lw et dh ctx cs dch γd γa cfg res γf γt γi n hrvu hbm
  wp_start as ⟨#Hfix, #Henv, #Hctx, #Hsctx, #HerrIs, Hst⟩
  ihave #Hklog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  ihave #Hlogr : isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr $$ []
  · iPkgInit
  ihave #Hfix2 := Hfix
  iunfold reflFixed at Hfix2
  icases Hfix2 with ⟨#Hf1, #Hf2, -⟩
  iunfold reflFixed1 at Hf1
  icases Hf1 with ⟨%c, -, -, -, -, -, #Huwl, -⟩
  iunfold reflFixed2 at Hf2
  icases Hf2 with ⟨%name, %td, %ps, %md, %sr, %weh, -, #Hname, #Htd, -, -, -, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_FromContext (GoInterface.ok ctx)) $$ [$Hklog] as %lg -
  · ipureintro; simp
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply (wp_V_ptr logger_ptr lg _ _) $$ [$Hlogr $logger] as %lg' logger
  (try wp_auto)
  wp_apply (wp_Info lg' _ _ _ _) $$ [$Hlogr $Hsl] as -
  (try wp_auto)
  wp_apply (wp_list r f lw et dh ctx dch γd γa cfg res γf γt γi n) $$ [$Hpkg $Hfix $Henv $Hsctx $Hst]
    as %err Hpost
  (try wp_auto)
  icases Hpost with (⟨%he, %k, Hst⟩ | ⟨%hne, Hst⟩ | ⟨%he, #Hseen⟩)
  · subst he
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply (wp_V_ptr logger_ptr lg _ _) $$ [$Hlogr $logger] as %lg' logger
    (try wp_auto)
    wp_apply (wp_Info lg' _ _ _ _) $$ [$Hlogr $Hsl] as -
    (try wp_auto)
    wp_apply (wp_watchWithResync r f lw et dh ctx cs dch γd γa cfg res γf γt γi k hrvu hbm)
      $$ [$Hpkg $Hfix $Henv $Hctx $Hsctx $HerrIs Hst] as %err2 Hpost
    · ileft; iexact Hst
    (try wp_auto)
    iapply HΦ
    unfold lwPost
    icases Hpost with (H | H)
    · ileft; iexact H
    · iright; iright; iexact H
  · cases err with
    | nil => exact absurd rfl hne
    | ok ei =>
      (try wp_auto)
      iapply HΦ
      unfold lwPost
      iright; ileft; iexact Hst
  · subst he
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply (wp_V_ptr logger_ptr lg _ _) $$ [$Hlogr $logger] as %lg' logger
    (try wp_auto)
    wp_apply (wp_Info lg' _ _ _ _) $$ [$Hlogr $Hsl] as -
    (try wp_auto)
    wp_apply (wp_watchWithResync r f lw et dh ctx cs dch γd γa cfg res γf γt γi 0 hrvu hbm)
      $$ [$Hpkg $Hfix $Henv $Hctx $Hsctx $HerrIs] as %err2 Hpost
    · iright; iexact Hseen
    (try wp_auto)
    iapply HΦ
    unfold lwPost
    icases Hpost with (H | H)
    · ileft; iexact H
    · iright; iright; iexact H

end proof

end cache
end EtcdGrove
end Perennial
