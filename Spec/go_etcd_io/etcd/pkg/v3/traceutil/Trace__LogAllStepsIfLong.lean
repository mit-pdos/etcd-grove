/-
`traceutil.Trace.LogAllStepsIfLong`: the trust boundary (`pkg/v3/traceutil` is names-only). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `t.LogAllStepsIfLong(threshold)` logs all the trace's steps if it took longer: it returns (on a non-nil trace). -/
abbrev traceutil.Trace.LogAllStepsIfLong.spec : Prop :=
  ∀ (t : Loc) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ ⌜t ≠ null⌝ }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"LogAllStepsIfLong")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
