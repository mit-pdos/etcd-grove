/- Lean-first (no Rocq counterpart).

# `svc.NewDriverClient`'s proof

The composite literal's one field.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.NewDriverClient

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Assumptions]

theorem NewDriverClient.wp_proof : NewDriverClient.spec (GF := GF) (hG := hG) := by
  intro cc
  wp_start
  wp_auto
  wp_alloc dc as Hd
  iStructNamed Hd
  ipersist cc
  wp_auto
  iapply HΦ
  iexists dc
  iframe
  isplitl []
  · ipureintro; rfl
  · iexact cc

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
