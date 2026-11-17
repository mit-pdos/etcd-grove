module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Equal
public import Spec.reflect.DeepEqualK8s
public import Spec.maps.Equal

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem RM_eq_iff (m1 m2 : RM) :
    m1 = m2 ↔ m1.items = m2.items ∧ m1.rv = m2.rv ∧ m1.pfx = m2.pfx ∧ m1.rewrites = m2.rewrites := by
  cases m1; cases m2; simp

theorem fmap_obj_inj (a b : GMap GoString github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)
    (h : GMap.fmap DeepV.obj a = GMap.fmap DeepV.obj b) : a = b := by
  apply GMap.map_eq
  intro k
  have := congrArg (· !! k) h
  simp only [GMap.lookup_fmap] at this
  cases ha : a !! k <;> cases hb : b !! k <;> simp_all

theorem Model.Equal.wp_proof
    (wp_DeepEqual : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG))
    (wp_MapsEqual : maps.Equal.spec_strBool (GF := GF) (hG := hG)) :
    Model.Equal.spec (GF := GF) (hG := hG) := by
  intro mp1 mp2 m1 m2
  wp_start as ⟨Hm1, Hm2⟩
  unfold modelAt modelRep
  icases Hm1 with ⟨#Hinit, %il1, %rl1, %M1, #Hp1, #HI1, #Hit1, #HR1⟩
  icases Hm2 with ⟨-, %il2, %rl2, %M2, #Hp2, #HI2, #Hit2, #HR2⟩
  iStructNamed Hp1
  iStructNamed Hp2
  wp_auto
  sorry

end proof

end k8s_correctness
end EtcdGrove
end Perennial
