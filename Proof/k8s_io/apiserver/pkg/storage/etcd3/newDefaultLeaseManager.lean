/-
Lean-first (no Rocq counterpart).

The proof of `newDefaultLeaseManager`: its object count defaulted, `newLeaseManager`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.newDefaultLeaseManager
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem newDefaultLeaseManager.wp_proof (wp_nlm : newLeaseManager.spec (GF := GF) (hG := hG)) :
    newDefaultLeaseManager.spec (GF := GF) (hG := hG) := by
  intro cl cfg
  wp_start
  wp_auto
  cases decide (sint.Z cfg.MaxObjectCount' ≤ sint.Z (W64 0))
  all_goals
    wp_auto
    wp_apply wp_nlm as %l -
    iapply HΦ
    itrivial

end proof

end k8s
end EtcdGrove
end Perennial
