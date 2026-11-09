/-
## `(*Trace).StepWithFunction(f, msg, fields...)`

**Users.** `txn.Txn` (`txn/txn.go:45`: the compare-and-check under the write transaction),
`txn.getPrevKV` (`put.go:106`: a range of the write transaction, which steps the same trace). The
function may use the trace: it is lent to it. Snippet: `trace.go` (`ReqRequestTrace`).

**Proof sketch.** `disableStep` (a store), `f()` with the trace lent (its `Step`s are no-ops),
`enableStep`, `Step`.

**Changes.** From `specs-ref`'s `Trace__StepWithFunction.lean` (the emptiness index dropped).

**Margin.** None.
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

/-- **Runs `f()` with the trace lent, then records a step**: `f`'s `Q`, the trace kept. -/
def Trace.StepWithFunction.spec : Prop :=
  ∀ (t : Loc) (f : GoFunc) (msg : GoString) (fields : GoSlice) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t ∗ fieldsOwn fields ∗
      (traceOwn t -∗ WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ traceOwn t ∗ Q }}) }}
    (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"StepWithFunction")) (Val #f)) (Val #msg)) (Val #fields))
  {{ RET #(); traceOwn t ∗ Q }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
