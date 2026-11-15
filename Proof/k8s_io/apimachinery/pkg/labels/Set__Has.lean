/-
Proof of `Spec/k8s_io/apimachinery/pkg/labels/Set__Has.lean`: the map lookup. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.labels.Set__Has

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
variable [package_sem : k8s_io.apimachinery.pkg.labels.Assumptions]

theorem labels.Set.Has.wp_proof : labels.Set.Has.spec (GF := GF) (hG := hG) := by
  intro m dq M k
  wp_start as Hm
  (try wp_auto)
  wp_apply (wp_map_lookup2 go.string go.string m M k dq) $$ [$Hm] as Hm
  (try wp_auto)
  iapply HΦ $$ Hm

end proof

end EtcdGrove
end Perennial
