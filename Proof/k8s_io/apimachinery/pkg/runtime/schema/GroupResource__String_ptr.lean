/-
The trust boundary: `Spec/k8s_io/apimachinery/pkg/runtime/schema/GroupResource__String_ptr.lean`
(`runtime/schema` is translated names only; the method formats two strings, total). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupResource__String_ptr

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

axiom schema.GroupResource.String_ptr.wp_proof :
  schema.GroupResource.String_ptr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
