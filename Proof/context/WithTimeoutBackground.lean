/-
The trust boundary: `context.WithTimeout(context.Background(), d)` returns a context
(`isContext`) and a callable `cancel` (Go's `WithDeadline` of `Background()`; Perennial proves
`WithDeadlineCause` for an `isContext` parent only, and `Background()` is none).
-/
module

public import Spec.context.WithTimeoutBackground

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
variable [package_sem : context.Assumptions]

axiom context.WithTimeoutBackground.wp_proof :
  context.WithTimeoutBackground.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
