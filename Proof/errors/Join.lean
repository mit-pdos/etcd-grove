/-
The trust boundary of `errors.Join` (see its spec).
-/
module

public import Spec.errors.Join

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom errors.Join.wp_proof : errors.Join.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
