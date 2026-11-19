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
first, so a nil receiver panics, `k8s.io/utils/trace/trace.go:161,207`). Opaque: Go's `New` returns
`&Trace{...}`, so `t ≠ null` is one reading of it; a model of `New` that returns `nil` reads it as
`True`. A pure fact, hence persistent. -/
opaque trace.fromNew : Loc → Prop

end EtcdGrove
end Perennial
