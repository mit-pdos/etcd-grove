module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.fieldSel__Empty

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

theorem fieldSel.Empty.wp_proof :
    fieldSel.Empty.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
