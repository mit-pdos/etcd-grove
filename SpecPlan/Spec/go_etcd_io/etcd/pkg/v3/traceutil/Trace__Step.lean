/-
## `(*Trace).Step(msg, fields...)`

**Users.** The request path (`v3_server.go:140,176,347,414,1048`), `txn` (`range.go:78,81`,
`txn.go:59`, ...), mvcc's transactions (`kvstore_txn.go:108,...`: the trace they were begun with),
the read loop (`read.go:126,142`). Snippets: `examples/specreq/pkgleaves/trace.go` (`ReqRequestTrace`, `ReqMvccTodoTrace`,
`ReqReadLoopTrace`).

**Proof sketch.** Unless steps are disabled, `time.Now()` and an append keeping the fields slice.

**Changes.** From `specs-ref`'s `Trace__Step.lean`. **Margin.** None.
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

/-- **Records a step** (unless steps are disabled); the trace kept. -/
def Trace.Step.spec : Prop :=
  ∀ (t : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t ∗ fieldsOwn fields }}
    (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"Step")) (Val #msg)) (Val #fields))
  {{ RET #(); traceOwn t }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
