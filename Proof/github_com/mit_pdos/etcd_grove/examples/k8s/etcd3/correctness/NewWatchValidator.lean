/-
Lean-first (no Rocq counterpart).

The proof of `NewWatchValidator`: the struct literal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewWatchValidator

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem NewWatchValidator.wp_proof : NewWatchValidator.spec (GF := GF) (hG := hG) := by
  intro rp
  wp_start as -
  wp_auto
  iapply HΦ; itrivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
