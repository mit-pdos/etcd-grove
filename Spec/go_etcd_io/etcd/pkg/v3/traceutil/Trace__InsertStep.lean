/-
`(*traceutil.Trace).InsertStep` (`trace.go`: inserts a step at `at` if `at < len(steps)`, else
appends). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
`notes/decisions.md`, "Traces on the request path"). A negative `at` panics (`t.steps[at:]`): `0 ≤ at`, as every caller.
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

/-- `t.InsertStep(at, st, msg, fields...)` of an owned trace, `at` not negative, the fields
owned: it returns; the trace kept (with the step). -/
abbrev traceutil.Trace.InsertStep.spec : Prop :=
  ∀ (t : Loc) (e : Bool) (at' : w64) (st : _root_.Perennial.time.Time) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ownTrace t e ∗ traceutil.ownFields fields ∗
      ⌜0 ≤ sint.Z at'⌝ }}
    (App (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"InsertStep")) (Val #at')) (Val #st)) (Val #msg))
      (Val #fields))
  {{ RET #(); traceutil.ownTrace t e }}

end spec

end EtcdGrove
end Perennial
