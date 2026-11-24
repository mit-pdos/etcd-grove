/-
`(*traceutil.Trace).logInfo` (`trace.go`: the message and zap fields `LogWithStepThreshold` logs).
Lean-first (no Rocq counterpart); traceutil-log (2026-11-23).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI _root_.Perennial.go_etcd_io.etcd.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- `t.logInfo(d)` of an owned trace returns the message and the zap fields; what is left of the
trace is its struct, with its logger nil or a zap logger (what `LogWithStepThreshold` reads next).
The rest is consumed: `logInfo` merges a subtrace's fields into its steps' with `append`, so the
steps' fields slices may then share their arrays. -/
abbrev traceutil.Trace.logInfo.spec : Prop :=
  ∀ (t : Loc) (e : Bool) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ownTrace t e }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"logInfo")) (Val #d))
  {{ (msg : GoString) (fs : GoSlice), RET (PairV #msg #fs);
      ∃ v : go_etcd_io.etcd.pkg.v3.traceutil.Trace, t ↦ v ∗ zapLoggerOrNil v.lg' }}

end spec

end EtcdGrove
end Perennial
