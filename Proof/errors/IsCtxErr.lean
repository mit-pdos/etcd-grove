/-
The trust boundary: `errors.Is` of a context's error against `context.Canceled` or
`context.DeadlineExceeded` (Perennial's `errors.wp_Is` needs the error's tree, which a context's
`Err` does not give, and a pointer target, which `DeadlineExceeded` is not). Go's `Is` compares
`err` with the target (no panic: the target's type, `*errorString` or the empty struct
`deadlineExceededError`, is comparable) and walks `err`'s `Is`/`Unwrap` methods, which the
standard contexts' errors (`Canceled`, `DeadlineExceeded`, or a parent's) do not have.
-/
module

public import Spec.errors.IsCtxErr

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
variable [package_sem : _root_.Perennial.errors.Assumptions]

axiom errors.IsCtxErr.wp_proof : errors.IsCtxErr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
