/-
The trust boundary: `Spec/k8s_io/apimachinery/pkg/runtime/schema/GroupVersionResource__Empty_ptr.lean` (the method compares three strings with `""`, total). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupVersionResource__Empty_ptr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.schema.Assumptions]

axiom schema.GroupVersionResource.Empty_ptr.wp_proof :
  schema.GroupVersionResource.Empty_ptr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
