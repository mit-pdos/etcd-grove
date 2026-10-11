/-
`(*traceutil.Trace).StartSubTrace`: the trust boundary (`pkg/v3/traceutil` is names-only). Lean-first.

`t.StartSubTrace(fields...)` appends a sub-trace start step of the trace `t` (not nil): bookkeeping for logs, no effect here.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.Proof.context

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

/-- `t.StartSubTrace(fields...)` (a trace not nil) returns. -/
abbrev traceutil.Trace.StartSubTrace.spec : Prop :=
  ∀ (t : Loc) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ ⌜t ≠ null⌝ }}
    (App (Val (t @!! go.GoType.PointerType traceutil.Trace.ty @!! go!"StartSubTrace")) (Val #fields))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
