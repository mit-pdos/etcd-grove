/-
Lean-first (no Rocq counterpart).

The proof of `newLeaseManager`: an allocation.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.newLeaseManager

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem newLeaseManager.wp_proof : newLeaseManager.spec (GF := GF) (hG := hG) := by
  intro cl rs pct moc
  wp_start
  wp_auto
  irename «$r0» => Hl
  generalize «$r0_ptr» = l at *
  iapply HΦ
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
