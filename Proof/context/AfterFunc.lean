/-
The trust boundary: `context.AfterFunc` (`Spec/context/AfterFunc.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.context.AfterFunc

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

/-- **The trust boundary**: `context.AfterFunc` (Go's `context.go:325`) registers `f` with the
context (with its `afterFuncer`, for a `*cancelCtx`, or with a goroutine waiting on `Done()`
otherwise) and, once the context is done, calls it in a goroutine of its own, at most once; the
returned `stop` unregisters it and returns whether it did. Perennial translates it but has no spec
of it: its proof needs `*afterFuncCtx`'s `cancel`, `sync.Once` and the `afterFuncer` type
assertion, which Perennial's context model does not cover (2026-10-17, etcd-io/etcd#21600's
`store.waitForRev` and `Cache.Watch`). The spec says less than Go does (`f` may run any number of
times, at any time), so it is sound for any context whose `Done` behaves as `isContext` says. -/
axiom context.AfterFunc.wp_proof : context.AfterFunc.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
