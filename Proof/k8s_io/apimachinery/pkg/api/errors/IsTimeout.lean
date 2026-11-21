/-
Proof of `apierrors.IsTimeout` (`Spec/k8s_io/apimachinery/pkg/api/errors/IsTimeout.lean`) over its body
(prove-k8s2, 2026-11-20; until then a trust-boundary axiom).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.IsTimeout
public import Spec.k8s_io.apimachinery.pkg.api.errors.reasonAndCodeForError
public import Proof.k8s_io.apimachinery.pkg.api.errors.Checks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem IsTimeout.wp_proof
    (wp_reasonAndCodeForError : reasonAndCodeForError.spec (GF := GF) (hG := hG)) :
    IsTimeout.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hok
  ihave Hfact : (_root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.apierrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hfact with ⟨%mp, #Hkr, #Hm⟩
  wp_auto
  wp_apply (wp_reasonAndCodeForError err) $$ [Hok] as %r %c #Hrc
  · iframe
    iexact Hok
  try wp_auto
  by_cases hr : r = go!"Timeout"
  · rw [decide_eq_true hr]
    wp_auto
    iapply HΦ
    iintro !> %w #Hw
    ihave %h := Hrc $$ Hw
    ipureintro
    cases w <;> obtain ⟨h1, h2⟩ := h <;> simp_all (config := {decide := true}) [timeoutV]
  · rw [decide_eq_false hr]
    wp_auto
    wp_apply (wp_map_lookup2 (K := GoString) (V := Unit)
      k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty (go.StructType []) mp knownReasonsMap r
      DFrac.discard) $$ [Hm] as -
    · iexact Hm
    rw [knownReasonsMap_lookup]
    try wp_auto
    by_cases hk : r ∈ knownReasons <;> by_cases hc : c = W32 504 <;>
      simp only [hk, _root_.decide_true, _root_.decide_false, Bool.not_true] <;> (try wp_auto) <;>
      (try simp only [hc, _root_.decide_true, _root_.decide_false]) <;>
      (try wp_auto) <;>
    · iapply HΦ
      iintro !> %w #Hw
      ihave %h := Hrc $$ Hw
      ipureintro
      cases w <;> obtain ⟨h1, h2⟩ := h <;> simp_all (config := {decide := true}) [timeoutV]

end proof

end apierrors
end EtcdGrove
end Perennial
