/-
Lean-first (no Rocq counterpart).

The proof of `objectRV`: `meta.Accessor`, the object's `GetResourceVersion`, the versioner's parse
(`parseRVD_rvStr`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.objectRV
public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__GetResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem objectRV.wp_proof
    (wp_Accessor : apimeta.Accessor.spec (GF := GF) (hG := hG))
    (wp_GetRV : k8s_etcd3.Obj.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_PRV : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG)) :
    objectRV.spec (GF := GF) (hG := hG) := by
  intro x o
  unfold deepRO
  wp_start as #Hx
  iunfold deepRep at Hx
  icases Hx with ⟨%p, %hx, #Hp⟩
  subst hx
  have hty := objTyOk_holds.2.2
  wp_auto
  wp_apply (wp_Accessor ⟨go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #p⟩ hty)
  wp_apply (wp_GetRV p DFrac.discard o) $$ [Hp]
  · iframe #
  iintro -
  wp_auto
  wp_apply (wp_PRV (rvStr o.ResourceVersion')) as %n %err Hr
  rw [parseRVD_rvStr]
  icases Hr with %Hr
  obtain ⟨rfl, rfl⟩ := Hr
  wp_auto
  iapply HΦ; itrivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
