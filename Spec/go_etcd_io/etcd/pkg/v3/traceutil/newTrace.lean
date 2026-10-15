/-
`traceutil.newTrace` (`trace.go`: a trace of the operation, its fields, started now). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
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

/-- `newTrace(op, lg, fields...)`, the fields owned: a fresh trace, owned, keeping them. -/
abbrev traceutil.newTrace.spec : Prop :=
  ∀ (op : GoString) (lg : Loc) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ownFields fields }}
    (App (App (App (Val (@! go_etcd_io.etcd.pkg.v3.traceutil.newTrace)) (Val #op)) (Val #lg)) (Val #fields))
  {{ (t : Loc), RET #t; ⌜t ≠ null⌝ ∗ traceutil.ownTrace t false }}

end spec

end EtcdGrove
end Perennial
