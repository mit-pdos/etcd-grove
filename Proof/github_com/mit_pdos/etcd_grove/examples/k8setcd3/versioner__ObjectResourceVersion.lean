module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner__ObjectResourceVersion


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

theorem versioner.ObjectResourceVersion.wp_proof  :
    versioner.ObjectResourceVersion.spec (GF := GF) (hG := hG) := by
  intro p dq name val rv
  wp_start as Hp
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  (try wp_auto)
  iapply HΦ
  iapply typedPointsto_combine p _ dq Hpn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end k8setcd3
end EtcdGrove
end Perennial
