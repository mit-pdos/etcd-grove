module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.validateFor

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Obj)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem validateFor.wp_proof : validateFor.spec (GF := GF) (hG := hG) := by
  intro reject
  wp_start as -
  iapply wp_fupd
  (try wp_auto)
  ipersist reject
  rw [recv_eq_func_mk]
  imodintro
  iapply HΦ
  iunfold validateD
  imodintro
  iintro %ctx %p %name %vl %n %Ψ Hp HΨ
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  wp_pure
  wp_pure
  iStructNamed Hp
  (try wp_auto)
  wp_if_destruct
  · have hr : rejects [] vl = false := rfl
    ihave Hp : p ↦ Obj.mk name vl n $$ [Name Value ResourceVersion]
    · iapply typedPointsto_combine p _ _ Hpn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    (try wp_auto)
    iapply HΨ $$ Hp
    rw [hr]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  · have hne := Hif
    (try wp_auto)
    wp_if_destruct
    · have hr : rejects reject vl = true := by simp [rejects, hne, Hif]
      ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      icases Hi with ⟨-, -, -, -, ⟨%eD, #HeD, -⟩, -⟩
      ihave Hp : p ↦ Obj.mk name vl n $$ [Name Value ResourceVersion]
      · iapply typedPointsto_combine p _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      (try wp_auto)
      iapply HΨ $$ Hp
      rw [hr]
      simp only [↓reduceIte]
      iexact HeD
    · have hr : rejects reject vl = false := by simp [rejects, Hif]
      ihave Hp : p ↦ Obj.mk name vl n $$ [Name Value ResourceVersion]
      · iapply typedPointsto_combine p _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      (try wp_auto)
      iapply HΨ $$ Hp
      rw [hr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial

end proof

end k8setcd3
end EtcdGrove
end Perennial
