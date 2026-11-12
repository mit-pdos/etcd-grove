/-
## `(*Trace).InsertStep(at, time, msg, fields...)`

**Users.** `raftRequest`, `Compact` (`v3_server.go:403,1027`: `at = 0`). Snippet: `examples/specreq/pkgleaves/trace.go`
(`ReqApplyTraceHandoff`).

**Proof sketch.** `at < len(steps)`: `append(steps[:at+1], steps[at:]...)` (in bounds for
`0 ≤ at`) and a store at `at`; else an append. The fields slice is kept in the step.

**Changes.** From `specs-ref`'s `Trace__InsertStep.lean`. The premise `0 ≤ at` stays: a negative
`at` panics (`steps[at:]`, or the store at `-1`); every caller passes `0`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- **Inserts a step** at `at` (not negative), or appends it; the trace kept. -/
def Trace.InsertStep.spec : Prop :=
  ∀ (t : Loc) (at' : w64) (st : _root_.Perennial.time.Time) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t ∗ fieldsOwn fields ∗ ⌜0 ≤ sint.Z at'⌝ }}
    (App (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"InsertStep")) (Val #at')) (Val #st)) (Val #msg)) (Val #fields))
  {{ RET #(); traceOwn t }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
