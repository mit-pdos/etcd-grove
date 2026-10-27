/-
Lean-first (no Rocq counterpart).

The proof of `corruptObjErrAggregatorFactory`: a closure, or `defaultListErrorAggregatorFactory`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.corruptObjErrAggregatorFactory

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

theorem corruptObjErrAggregatorFactory.wp_proof : corruptObjErrAggregatorFactory.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  cases decide (sint.Z n ≤ sint.Z (W64 0))
  · wp_auto
    rw [recv_eq_func_mk]
    iapply HΦ
    itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end k8s
end EtcdGrove
end Perennial
