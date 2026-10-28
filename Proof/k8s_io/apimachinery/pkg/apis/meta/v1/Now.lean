/-
Proof of `Spec/k8s_io/apimachinery/pkg/apis/meta/v1/Now.lean`: `time.Now()`, wrapped. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.Now
public import Perennial.Spec.time.Now

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metav1

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

theorem Now.wp_proof (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    Now.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_Now as %t -
  iapply HΦ
  itrivial

end proof

end metav1
end EtcdGrove
end Perennial
