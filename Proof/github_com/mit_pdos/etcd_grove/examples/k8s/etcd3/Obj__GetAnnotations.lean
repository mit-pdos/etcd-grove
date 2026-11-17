module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__GetAnnotations

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Obj.GetAnnotations.wp_proof :
    Obj.GetAnnotations.spec (GF := GF) (hG := hG) := by
  intro p dq v
  wp_start as Hp
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  (try wp_auto)
  cases ha : v.Annotated'
  · wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitl
    · iapply typedPointsto_combine p _ dq Hpn
      simp only [TypedPointsto.typedPointstoDef]
      rw [ha]
      iframe
    · ipureintro; trivial
  · wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mref Hm
    wp_apply (wp_mapInsert (K := GoString) (V := GoString) go.string) $$ Hm as Hm
    iapply HΦ
    simp only [↓reduceIte]
    iframe Hm
    iapply typedPointsto_combine p _ dq Hpn
    simp only [TypedPointsto.typedPointstoDef]
    rw [ha]
    iframe

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
