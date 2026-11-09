/-
## `(*Trace).StartSubTrace(fields...)`

**Users.** `txn.executeTxn` (`txn/txn.go:146`), per request op. Snippet: `trace.go` (`ReqSubTrace`).

**Proof sketch.** An append of a step keeping the fields slice. **Changes.** From `specs-ref`'s
`Trace__StartSubTrace.lean`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api

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

/-- Appends a sub-trace marker with the fields; the trace kept. -/
def Trace.StartSubTrace.spec : Prop :=
  ∀ (t : Loc) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t ∗ fieldsOwn fields }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"StartSubTrace")) (Val #fields))
  {{ RET #(); traceOwn t }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
