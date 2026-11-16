/-
Proof of `Spec/k8s_io/apiserver/pkg/util/flowcontrol/initializationSignalFrom.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.util.flowcontrol.initializationSignalFrom

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.util.flowcontrol.Assumptions]

theorem flowcontrol.initializationSignalFrom.wp_proof :
    flowcontrol.initializationSignalFrom.spec (GF := GF) (hG := hG) := by
  intro ci
  wp_start as #Hv
  wp_auto
  unfold context.valueAt
  wp_apply Hv as %v %hv
  cases v with
  | nil =>
    wp_auto
    iapply HΦ; ipureintro; rfl
  | ok vi =>
    rcases hv with h | hv
    · cases h
    have h := hv vi rfl
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
