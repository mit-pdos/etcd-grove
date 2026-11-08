module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.validateFor

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Obj)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem validateFor.wp_proof : validateFor.spec (GF := GF) (hG := hG) := by
  intro has reject
  wp_start as -
  iapply wp_fupd
  (try wp_auto)
  ipersist rejects
  ipersist reject
  imodintro
  iapply HΦ
  iunfold validateD
  imodintro
  iintro %ctx %p %v %Ψ Hp HΨ
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  wp_pure
  wp_pure
  iStructNamed Hp
  (try wp_auto)
  cases hh : has
  · have hr : rejects false reject v.Node' = false := rfl
    ihave Hp : p ↦ v $$ [Namespace Name UID Value Node App ResourceVersion]
    · iapply typedPointsto_combine p _ _ Hpn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    (try wp_auto)
    iapply HΨ $$ Hp
    rw [hr]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  · (try wp_auto)
    by_cases hn : v.Node' = reject
    · have hr : rejects true reject v.Node' = true := by simp [rejects, hn]
      rw [decide_eq_true hn]
      ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      icases Hi with ⟨-, -, -, ⟨%eD, #HeD, -⟩, -⟩
      ihave Hp : p ↦ v $$ [Namespace Name UID Value Node App ResourceVersion]
      · iapply typedPointsto_combine p _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      (try wp_auto)
      iapply HΨ $$ Hp
      rw [hr]
      simp only [↓reduceIte]
      iexact HeD
    · have hr : rejects true reject v.Node' = false := by simp [rejects, hn]
      rw [decide_eq_false hn]
      ihave Hp : p ↦ v $$ [Namespace Name UID Value Node App ResourceVersion]
      · iapply typedPointsto_combine p _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      (try wp_auto)
      iapply HΨ $$ Hp
      rw [hr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
