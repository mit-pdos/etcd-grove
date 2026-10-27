/-
The trust boundary of `fields.Everything` (see its spec).
-/
module

public import Spec.k8s_io.apimachinery.pkg.fields.Everything

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom fields.Everything.wp_proof : fields.Everything.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
