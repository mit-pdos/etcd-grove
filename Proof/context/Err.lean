/-
The trust boundary: the error a context's `Err()` returns has an `Error()` that returns some
string (`Spec/context/Err.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.Err

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
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **The trust boundary**: `ctx.Err()` behaves as `isContext` says (`"#HErr"`), and the
`Error()` of the non-nil error it returns returns some string, touching no memory the caller
owns. True of the standard library's contexts: their `Err()` returns `context.Canceled` (an
`errors.New` `*errorString`) or `context.DeadlineExceeded` (a `deadlineExceededError`, whose
`Error` returns a constant); a cancel cause is `context.Cause`'s, not `Err()`'s. gRPC's request
contexts are standard-library contexts. Assumed of a user-defined `Context`, of whose `Err()`
Go's `Context` contract asks only that it be an error explaining why `Done` is closed. -/
axiom context.Err.wp_proof : context.Err.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
