/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/rvString.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.rvString
public import Spec.strconv.FormatUint

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

theorem rvString.wp_proof (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    rvString.spec (GF := GF) (hG := hG) := by
  intro _ n
  wp_start
  wp_auto
  wp_apply wp_FormatUint as %str %Hstr
  · ipureintro; decide
  subst Hstr
  unfold rvStr decStr
  iapply HΦ
  itrivial

end proof

end apimodel
end EtcdGrove
end Perennial
