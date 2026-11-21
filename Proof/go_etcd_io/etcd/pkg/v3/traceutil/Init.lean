/-
Package initialization of `go_etcd_io.etcd.pkg.v3.traceutil`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`traceutilInit`, `storage/mvcc/Base.lean`): `Tracer` holds a fixed tracer. Its
variables' initializers are untranslated: the trust-boundary axiom `Tracer_init` states the one
the fact reads (`trace.go`), `opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.time.Link
public import Proof.go_uber_org.zap.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.pkg.v3.traceutil
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `Tracer = noop.NewTracerProvider().Tracer(instrumentationScope)` (`trace.go`): a `trace.Tracer`. -/
axiom Tracer_init :
    {{ (True : IProp GF) }} (App (Val Tracer.init) (Val #()))
    {{ RET #(); ∃ tr : GoInterfaceOk, globalAddr Tracer ↦ GoInterface.ok tr }}

end go_etcd_io.etcd.pkg.v3.traceutil
end opaqueInits

end Perennial
