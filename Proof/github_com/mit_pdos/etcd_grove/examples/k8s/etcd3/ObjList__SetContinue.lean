module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList__SetContinue

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

theorem ObjList.SetContinue.wp_proof :
    ObjList.SetContinue.spec (GF := GF) (hG := hG) := by
  intro p v c
  wp_start as Hp
  wp_auto
  iapply HΦ
  iframe

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
