/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControlleeExpectations__GetExpectations.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControlleeExpectations__GetExpectations
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode k8s_io.kubernetes.pkg.controller

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

theorem ControlleeExpectations.GetExpectations.wp_proof :
    ControlleeExpectations.GetExpectations.spec (GF := GF) (hG := hG) := by
  intro e k
  wp_start as #Hce
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold isCE at Hce
  icases Hce with ⟨#Hk, ⟨%t, #Ht⟩, #Hinv⟩
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 _ _ $$ %_ Hat
  iinv Hinv with ⟨%a, %d, >Ha, >Hd⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists a
  iframe Ha
  iintro Ha
  imod Hmask
  imod Hclose $$ [Ha Hd] with -
  · inext; iexists _, _; iframe
  imodintro
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 _ _ $$ %_ Hat
  iinv Hinv with ⟨%a', %d', >Ha, >Hd⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists d'
  iframe Hd
  iintro Hd
  imod Hmask
  imod Hclose $$ [Ha Hd] with -
  · inext; iexists _, _; iframe
  imodintro
  wp_auto
  iapply HΦ; itrivial

end proof

end dsctl
end EtcdGrove
end Perennial
