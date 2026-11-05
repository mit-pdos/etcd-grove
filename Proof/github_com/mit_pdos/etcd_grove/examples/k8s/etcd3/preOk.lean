module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.preOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvString

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem preOk.wp_proof (wp_rvString : rvString.spec (GF := GF) (hG := hG)) :
    preOk.spec (GF := GF) (hG := hG) := by
  intro x o
  wp_start as -
  -- Stage 7b: Prove phase (two tests, `rvString`).
  sorry

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
