module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__SetResourceVersion
public import Perennial.Spec.strconv.ParseUint


@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Obj.SetResourceVersion.wp_proof
    (wp_ParseUint : _root_.Perennial.strconv.ParseUint.spec (GF := GF) (hG := hG)) :
    Obj.SetResourceVersion.spec (GF := GF) (hG := hG) := by
  intro p v s
  wp_start as Hp
  wp_auto
  by_cases hs : s = []
  · subst hs
    wp_auto
    iapply HΦ
    rw [show setRVL [] v.ResourceVersion' = W64 0 by simp [setRVL]]
    iexact Hp
  · rw [decide_eq_false hs]
    wp_auto
    wp_apply (wp_ParseUint s (W64 10) (W64 64) (by decide) (by decide) (by decide) (by decide))
      as %x %err Hr
    have h10 : sint.nat (W64 10) = 10 := rfl
    have h64 : sint.nat (W64 64) = 64 := rfl
    cases hpu : internal.strconv.parseUint s 10 64 with
    | ok n =>
      isimp [h10, h64, hpu] at Hr
      icases Hr with %hr
      obtain ⟨rfl, rfl⟩ := hr
      wp_auto
      iapply HΦ
      rw [show setRVL s v.ResourceVersion' = W64 n by simp [setRVL, hs, hpu]]
      iframe
    | errSyntax =>
      isimp [h10, h64, hpu] at Hr
      icases Hr with ⟨%hx, Hn⟩
      iunfold _root_.Perennial.strconv.numErrorOf at Hn
      icases Hn with ⟨%l, %e, %he, -, -⟩
      subst he
      wp_auto
      iapply HΦ
      rw [show setRVL s v.ResourceVersion' = v.ResourceVersion' by simp [setRVL, hs, hpu]]
      iexact Hp
    | errRange =>
      isimp [h10, h64, hpu] at Hr
      icases Hr with ⟨%hx, Hn⟩
      iunfold _root_.Perennial.strconv.numErrorOf at Hn
      icases Hn with ⟨%l, %e, %he, -, -⟩
      subst he
      wp_auto
      iapply HΦ
      rw [show setRVL s v.ResourceVersion' = v.ResourceVersion' by simp [setRVL, hs, hpu]]
      iexact Hp

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
