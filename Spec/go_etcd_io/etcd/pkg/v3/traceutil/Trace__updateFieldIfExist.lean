/-
`(*traceutil.Trace).updateFieldIfExist` (`trace.go`: the first field of the key gets the value). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
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

/-- `t.updateFieldIfExist(f)` of an owned trace, the value formattable: some boolean; the trace
kept. -/
abbrev traceutil.Trace.updateFieldIfExist.spec : Prop :=
  ∀ (t : Loc) (e : Bool) (f : traceutil.Field),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ownTrace t e ∗ ⌜traceutil.fieldsWf [f]⌝ }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"updateFieldIfExist")) (Val #f))
  {{ (b : Bool), RET #b; traceutil.ownTrace t e }}

end spec

end EtcdGrove
end Perennial
