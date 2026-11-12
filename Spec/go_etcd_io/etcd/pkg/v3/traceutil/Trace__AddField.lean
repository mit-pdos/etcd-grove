/-
`(*traceutil.Trace).AddField` (`trace.go`: each field updated in place or appended). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
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

/-- `t.AddField(fields...)` of an owned trace, the fields read (their values formattable): it
returns; the trace kept. -/
abbrev traceutil.Trace.AddField.spec : Prop :=
  ∀ (t : Loc) (e : Bool) (fields : GoSlice) (fs : List traceutil.Field) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceutil.ownTrace t e ∗ fields ↦*{dq} fs ∗
      ⌜traceutil.fieldsWf fs⌝ }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"AddField")) (Val #fields))
  {{ RET #(); traceutil.ownTrace t e ∗ fields ↦*{dq} fs }}

end spec

end EtcdGrove
end Perennial
