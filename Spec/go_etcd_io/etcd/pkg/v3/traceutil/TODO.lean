/-
`traceutil.TODO` (`trace.go`: `&Trace{isEmpty: true}`). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
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

/-- `traceutil.TODO()` returns a fresh trace, owned (an empty one, used where no trace is
wanted). -/
abbrev traceutil.TODO.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil }}
    (App (Val (@! traceutil.TODO)) (Val #()))
  {{ (t : Loc), RET #t; ⌜t ≠ null⌝ ∗ traceutil.ownTrace t true }}

end spec

end EtcdGrove
end Perennial
