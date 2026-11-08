module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.listOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.matchOpt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.predicate

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem listOptions.wp_proof
    (wp_matchOpt : matchOpt.spec (GF := GF) (hG := hG))
    (wp_predicate : predicate.spec (GF := GF) (hG := hG)) :
    listOptions.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as -
  wp_auto
  wp_apply wp_matchOpt
  wp_apply wp_predicate
  wp_auto
  iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
