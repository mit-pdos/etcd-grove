module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.updated

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Obj)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem updated.wp_proof : updated.spec (GF := GF) (hG := hG) := by
  intro inp p dq name vl n
  wp_start as Hp
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  (try wp_auto)
  iStructNamed «in»
  wp_if_destruct
  · -- `in.Reject` empty: not rejected
    have hr : rejects inp.Reject' vl = false := by
      simp [rejects, Hif]
    ihave Hp : p ↦{dq} Obj.mk name vl n $$ [Name Value ResourceVersion]
    · iapply typedPointsto_combine p _ dq Hpn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    (try wp_auto)
    icases (typedPointsto_not_null_dup _ _ _) $$ c with ⟨c, %Hcn⟩
    iStructNamed c
    cases hno : inp.NoOp'
    · (try wp_auto)
      iapply HΦ
      rw [hr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hp
      isplitr
      · ipureintro; simp [Hcn]
      iapply typedPointsto_combine c_ptr _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef, updObj, hno, Bool.false_eq_true, ↓reduceIte]
      iframe
    · (try wp_auto)
      iapply HΦ
      rw [hr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hp
      isplitr
      · ipureintro; simp [Hcn]
      iapply typedPointsto_combine c_ptr _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef, updObj, hno, ↓reduceIte]
      iframe
  · have hne := Hif
    (try wp_auto)
    wp_if_destruct
    · -- rejected
      have hr : rejects inp.Reject' inp.Reject' = true := by
        simp [rejects, hne]
      ihave Hp : p ↦{dq} Obj.mk name inp.Reject' n $$ [Name Value ResourceVersion]
      · iapply typedPointsto_combine p _ dq Hpn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      icases Hi with ⟨-, -, -, -, -, ⟨%eU, #HeU, -⟩⟩
      (try wp_auto)
      iapply HΦ
      rw [hr]
      simp only [↓reduceIte]
      iframe Hp
      iexact HeU
    · have hr : rejects inp.Reject' vl = false := by
        simp [rejects, Hif]
      ihave Hp : p ↦{dq} Obj.mk name vl n $$ [Name Value ResourceVersion]
      · iapply typedPointsto_combine p _ dq Hpn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      (try wp_auto)
      icases (typedPointsto_not_null_dup _ _ _) $$ c with ⟨c, %Hcn⟩
      iStructNamed c
      cases hno : inp.NoOp'
      · (try wp_auto)
        iapply HΦ
        rw [hr]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hp
        isplitr
        · ipureintro; simp [Hcn]
        iapply typedPointsto_combine c_ptr _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef, updObj, hno, Bool.false_eq_true, ↓reduceIte]
        iframe
      · (try wp_auto)
        iapply HΦ
        rw [hr]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hp
        isplitr
        · ipureintro; simp [Hcn]
        iapply typedPointsto_combine c_ptr _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef, updObj, hno, ↓reduceIte]
        iframe

end proof

end k8setcd3
end EtcdGrove
end Perennial
