/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/replaceRevision.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.replaceRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem replaceRevision.wp_proof : replaceRevision.spec (GF := GF) (hG := hG) := by
  intro _ x y st req
  wp_start as ⟨Hx, Hy, %Hr⟩
  wp_auto
  iapply HΦ
  iright
  iexists req
  iframe Hy
  ipureintro
  exact ⟨rfl, Hr.2⟩

end proof

end apimodel
end EtcdGrove
end Perennial
