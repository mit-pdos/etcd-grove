/-
The shared vocabulary of `k8s.io/utils/trace`'s boundary specs (`Spec/k8s_io/utils/trace/`).
-/
module

public import GeneratedProof.k8s_io.utils.trace

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- `trace.fromNew t`: `t` is a trace `trace.New` returned, which `(*Trace).Step` and
`(*Trace).LogIfLong` require (2026-11-18: their specs took any pointer, but both lock `t.lock`
first, so a nil receiver panics, `k8s.io/utils/trace/trace.go:161,207`). Go's `New` returns
`&Trace{...}` (`trace.go:154-156`): a non-nil pointer, which is what the two methods need (any
non-nil `*Trace` of a Go program is a `Trace`, whose zero value they accept: a zero `RWMutex`, a nil
`traceItems` that `Step` allocates). (prove-otel4, 2026-11-21: defined, where it was opaque, so that
`New`'s spec is proved over the real code; notes/specs-only/ledger.md.) A pure fact, hence persistent. -/
def trace.fromNew (t : Loc) : Prop := t ≠ null

end EtcdGrove
end Perennial
