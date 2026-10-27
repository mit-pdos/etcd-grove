/-
`(*traceutil.Trace).StepWithFunction` (`trace.go`: steps disabled, `f()`, enabled, one step). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
`notes/decisions.md`, "Traces on the request path").
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- `t.StepWithFunction(f, msg, fields...)` of an owned trace, the fields owned, runs `f()`
with the trace (`f` may use it: its steps are disabled meanwhile), `f()` returning; then it
returns, with `f`'s `Q`; the trace kept (`f` may hand it back at any emptiness: `isEmpty` is
written only at a trace's creation, but a caller that keeps it in a transaction's predicate,
`mvcc.isTxn`, knows it only up to it). -/
abbrev traceutil.Trace.StepWithFunction.spec : Prop :=
  ∀ (t : Loc) (e : Bool) (f : GoFunc) (msg : GoString) (fields : GoSlice) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ownTrace t e ∗ traceutil.ownFields fields ∗
      (traceutil.ownTrace t e -∗
        WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ Q ∗ ∃ e', traceutil.ownTrace t e' }}) }}
    (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"StepWithFunction")) (Val #f)) (Val #msg)) (Val #fields))
  {{ RET #(); Q ∗ ∃ e', traceutil.ownTrace t e' }}

end spec

end EtcdGrove
end Perennial
