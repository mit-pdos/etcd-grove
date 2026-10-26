module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner__UpdateObject


@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem versioner.UpdateObject.wp_proof  :
    versioner.UpdateObject.spec (GF := GF) (hG := hG) := by
  intro p name val rv n
  wp_start as Hp
  (try wp_auto)
  iapply HΦ
  iexact Hp

end proof

end k8setcd3
end EtcdGrove
end Perennial
