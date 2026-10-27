/-
`(*traceutil.Trace).LogAllStepsIfLong` (`trace.go`: logs all the trace's steps if it took longer). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
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

/-- `t.LogAllStepsIfLong(d)` of an owned trace returns. The trace is consumed: the logger's `logInfo`
merges a subtrace's fields into its steps' with `append`, so the steps' fields slices may then
share their arrays (each caller logs a trace last). -/
abbrev traceutil.Trace.LogAllStepsIfLong.spec : Prop :=
  ∀ (t : Loc) (e : Bool) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ownTrace t e }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"LogAllStepsIfLong")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
