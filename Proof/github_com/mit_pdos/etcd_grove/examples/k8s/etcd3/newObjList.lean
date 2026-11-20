module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObjList

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem newObjList.wp_proof : newObjList.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_alloc p as Hp
  wp_auto
  iapply HΦ
  iexact Hp

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
