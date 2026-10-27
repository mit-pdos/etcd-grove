/-
Proof of `Spec/k8s_io/client_go/tools/cache/parseRVForMetricsWithTruncation.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.parseRVForMetricsWithTruncation
public import Spec.strconv.ParseInt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem parseRVForMetricsWithTruncation.wp_proof
    (wp_ParseInt : strconv.ParseInt.spec (GF := GF) (hG := hG)) :
    parseRVForMetricsWithTruncation.spec (GF := GF) (hG := hG) := by
  intro rv
  wp_start
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ; itrivial
  · (try wp_auto)
    wp_func_call
    wp_call
    by_cases hl : rv.length < 2 ^ 63
    case neg => simp only [hl, ↓reduceIte]; wp_apply wp_AngelicExit
    simp only [hl, ↓reduceIte]
    wp_auto
    wp_if_destruct
    · (try wp_auto)
      wp_func_call
      wp_call
      simp only [hl, ↓reduceIte]
      (try wp_auto)
      wp_func_call
      wp_call
      simp only [hl, ↓reduceIte]
      (try wp_auto)
      have hb : 0 ≤ sint.Z (W64 (rv.length : Int) - W64 15) ∧
          sint.Z (W64 (rv.length : Int) - W64 15) ≤ sint.Z (W64 (rv.length : Int)) ∧
          sint.Z (W64 (rv.length : Int)) ≤ rv.length := by
        refine ⟨by word, by word, by word⟩
      simp only [hb, _root_.and_self, ↓reduceIte]
      (try wp_auto)
      wp_apply wp_ParseInt as %n %err _
      (try wp_auto)
      iapply HΦ; itrivial
    · (try wp_auto)
      wp_apply wp_ParseInt as %n %err _
      (try wp_auto)
      iapply HΦ; itrivial

end proof

end cache
end EtcdGrove
end Perennial
