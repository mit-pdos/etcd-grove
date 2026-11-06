module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.invalidObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem invalidObj.wp_proof (wp_storeKey : storeKey.spec (GF := GF) (hG := hG)) :
    invalidObj.spec (GF := GF) (hG := hG) := by
  intro key
  wp_start as -
  wp_auto
  wp_apply wp_storeKey
  simp only [invalidObjL, mkeyL]
  iapply HΦ
  (try ipureintro; trivial)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
