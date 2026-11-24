/-
`traceutil.writeFields` (`trace.go`: the fields formatted into a `strings.Builder`). Lean-first (no
Rocq counterpart); traceutil-log (2026-11-23), a callee of `logInfo`.
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

/-- `writeFields(sl)` of fields whose values are formattable (`fieldsWf`), read at any fraction,
returns some string. -/
abbrev traceutil.writeFields.spec : Prop :=
  ∀ (sl : GoSlice) (fs : List traceutil.Field) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ sl ↦*{dq} fs ∗
      ⌜traceutil.fieldsWf fs⌝ }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.traceutil.writeFields)) (Val #sl))
  {{ (s : GoString), RET #s; sl ↦*{dq} fs }}

end spec

end EtcdGrove
end Perennial
