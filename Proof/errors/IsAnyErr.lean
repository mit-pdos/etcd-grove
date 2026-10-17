/-
The trust boundary: `errors.Is` of any error against a pointer-error target returns (etcd#22387's
`Mutex.Lock` and `Election.Campaign`). Go's `Is` compares `err` with the target (no panic: a
pointer type is comparable) and walks `err`'s `Unwrap` chain, calling each error's `Is(error)
bool` method if it has one; it returns as long as those methods return and the chain is finite.
True of the errors `waitDeletes` returns: the standard contexts' errors and the package's
`errors.New` errors have neither method; the client's are gRPC status errors (whose `Is` compares
statuses), `rpctypes.EtcdError`s and context errors. A caller-supplied context whose `Err` returns
an error with a diverging or panicking `Is`/`Unwrap` is outside it.
-/
module

public import Spec.errors.IsAnyErr

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

/-- **Trust boundary**: `errors.Is` of any error, against a pointer error, returns. -/
axiom errors.IsAnyErr.wp_proof : errors.IsAnyErr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
