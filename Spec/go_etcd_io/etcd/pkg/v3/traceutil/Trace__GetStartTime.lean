/-
`(*traceutil.Trace).GetStartTime` (`trace.go`: `t.startTime`). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- `t.GetStartTime()` of an owned trace: some time; the trace kept. -/
abbrev traceutil.Trace.GetStartTime.spec : Prop :=
  ∀ (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ownTrace t e }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"GetStartTime")) (Val #()))
  {{ (st : _root_.Perennial.time.Time), RET #st; traceutil.ownTrace t e }}

end spec

end EtcdGrove
end Perennial
