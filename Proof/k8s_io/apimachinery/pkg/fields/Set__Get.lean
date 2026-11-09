/-
Proof of `Spec/k8s_io/apimachinery/pkg/fields/Set__Get.lean`: the map lookup. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.fields.Set__Get

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
variable [package_sem : k8s_io.apimachinery.pkg.fields.Assumptions]

theorem fields.Set.Get.wp_proof : fields.Set.Get.spec (GF := GF) (hG := hG) := by
  intro m dq M k
  wp_start as Hm
  (try wp_auto)
  wp_apply (wp_map_lookup1 go.string go.string m M k dq) $$ [$Hm] as Hm
  (try wp_auto)
  iapply HΦ $$ Hm

end proof

end EtcdGrove
end Perennial
