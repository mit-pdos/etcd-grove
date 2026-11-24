/-
Proof of `labels.Everything`'s spec over its translated body (#25, 2026-11-21; until then a
trust-boundary axiom): it loads `sharedEverythingSelector`, an empty `internalSelector` (`labels`'
fact, `labelsInit`), whose `Empty()` is `true`; `MatchesNothing` compares it with
`sharedNothingSelector`, a `nothingSelector`: different dynamic types, so `false` (Go's interface
comparison, Perennial's `go_eq_interface`). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.labels.Everything

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.labels.Assumptions]

theorem labels.Everything.wp_proof : labels.Everything.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave #Hfact : (k8s_io.apiserver.pkg.storage.etcd3.labelsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold k8s_io.apiserver.pkg.storage.etcd3.labelsInit at Hfact
  icases Hfact with ⟨⟨%p, #HE⟩, ⟨%vn, #HN⟩⟩
  wp_auto
  iapply HΦ
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · -- `MatchesNothing(s)`: `s == sharedNothingSelector`, of different dynamic types
    imodintro
    iintro %Φ' - HΦ'
    wp_func_call; wp_call
    wp_auto
    have hne : k8s_io.apimachinery.pkg.labels.internalSelector.ty ≠
        k8s_io.apimachinery.pkg.labels.nothingSelector.ty := by
      unfold k8s_io.apimachinery.pkg.labels.internalSelector.ty
        k8s_io.apimachinery.pkg.labels.nothingSelector.ty
      simp
    iapply HΦ'; itrivial
  · -- `internalSelector{}.Empty()`: `true` on both paths
    imodintro
    iintro %Φ' - HΦ'
    wp_method_call; wp_call
    wp_auto
    wp_if_destruct
    · iapply HΦ'; itrivial
    · iapply HΦ'; itrivial

end proof

end EtcdGrove
end Perennial
