/-
The trust boundary: a done context's `Err()` is `context.Canceled` or `context.DeadlineExceeded`
(Go's documented contract of `Context.Err`, which the standard contexts keep: a `cancelCtx` is
cancelled with `Canceled`, a `timerCtx` with `DeadlineExceeded`, a child with its parent's
`Err()`; Perennial's `isContext` keeps only that it is a typed error).
-/
module

public import Spec.context.ErrDone

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

axiom context.ErrDone.wp_proof : context.ErrDone.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
