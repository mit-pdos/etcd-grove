module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.tryUpdateFor
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

theorem tryUpdateFor.wp_proof (wp_updated : updated.spec (GF := GF) (hG := hG)) :
    tryUpdateFor.spec (GF := GF) (hG := hG) := by
  intro inp
  wp_start as -
  iapply wp_fupd
  (try wp_auto)
  ipersist «in»
  rw [recv_eq_func_mk]
  imodintro
  iapply HΦ
  iunfold tryUpdateD
  imodintro
  iintro %x %o %r %Ψ Ho HΨ
  iunfold objAtD at Ho
  icases Ho with ⟨%p, %n, %Hx, Hp⟩
  obtain ⟨rfl, Hpn, Hrv⟩ := Hx
  wp_pure
  (try wp_auto)
  wp_apply wp_updated inp p (DFrac.own 1) o.1.1 o.1.2 n $$ [$Hp] as %q %err ⟨-, Hres⟩
  cases hr : rejects inp.Reject' o.1.2
  · isimp only [hr, Bool.false_eq_true, ↓reduceIte] at Hres
    icases Hres with ⟨%Herr, Hq⟩
    obtain ⟨rfl, Hqn⟩ := Herr
    (try wp_auto)
    iapply HΨ
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    isplitr
    · ipureintro; simp
    iunfold objAtD
    iexists q, n
    simp only [updObj]
    iframe Hq
    ipureintro; simp [Hqn, Hrv]
  · isimp only [hr, ↓reduceIte] at Hres
    ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hi with ⟨-, -, -, -, -, #HeU⟩
    ihave #Hres := Hres
    ihave %Hne := errVar_ne_nil _ err $$ [$HeU $Hres]
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      (try wp_auto)
      iapply HΨ
      simp only [hr, ↓reduceIte]
      iexact Hres

end proof

end k8setcd3
end EtcdGrove
end Perennial
