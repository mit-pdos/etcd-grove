/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/dsmain/newNode.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: the composite literals.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.newNode

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI Iris.ProofMode apimodel dsctl informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Assumptions]

theorem newNode.wp_proof :
    newNode.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsmain
end EtcdGrove
end Perennial
