/-
Proof of `Spec/k8s_io/client_go/tools/cache/ObjectName__String.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.ObjectName__String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem ObjectName.String.wp_proof : ObjectName.String.spec (GF := GF) (hG := hG) := by
  intro on
  wp_start
  wp_auto
  wp_func_call
  wp_call
  by_cases hl : on.Namespace'.length < 2 ^ 63
  case neg => rw [if_neg hl]; wp_apply wp_AngelicExit
  rw [if_pos hl]
  wp_auto
  have hz : sint.Z (W64 (on.Namespace'.length : Int)) = on.Namespace'.length := by word
  wp_if_destruct
  · have hne : on.Namespace' ≠ [] := by
      intro h; rw [hz, h] at Hif; simp at Hif
    unfold nameKey; rw [if_neg hne]
    iapply HΦ; itrivial
  · have he : on.Namespace' = [] := by
      have h1 : ¬ (0 : Int) < on.Namespace'.length := by
        rw [← hz]; simpa [show sint.Z (W64 0) = 0 from rfl] using Hif
      exact List.eq_nil_of_length_eq_zero (by omega)
    unfold nameKey; rw [if_pos he]
    iapply HΦ; itrivial

end proof

end cache
end EtcdGrove
end Perennial
