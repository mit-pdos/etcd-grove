/-
The trust boundary: a context's `Err()` is `nil` until it is done, then `context.Canceled` or
`context.DeadlineExceeded` (Go's documented contract of `Context.Err`, which the standard contexts
keep; Perennial's `isContext` keeps only that a done context's error is typed).
-/
module

public import Spec.context.ErrAny

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

axiom context.ErrAny.wp_proof : context.ErrAny.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
