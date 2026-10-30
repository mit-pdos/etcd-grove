/-
Proof of `Spec/k8s_io/apimachinery/pkg/apis/meta/v1/Time__Equal.lean`: both non-nil, `time.Time.Equal`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.Time__Equal
public import Perennial.Spec.time.Time__Equal

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

theorem Time.Equal.wp_proof (wp_Equal : time.Time.Equal.spec (GF := GF) (hG := hG)) :
    Time.Equal.spec (GF := GF) (hG := hG) := by
  intro a b ta tb
  wp_start as ⟨Ha, Hb⟩
  ihave %Hna := typedPointsto_not_null _ _ _ $$ Ha
  ihave %Hnb := typedPointsto_not_null _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hna
  simp only [decide_eq_false Hna, Bool.not_false]
  wp_auto
  simp only [decide_eq_false Hnb, Bool.not_false]
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_Equal as %eq -
  iapply HΦ
  iframe

end proof

end metav1
end EtcdGrove
end Perennial
