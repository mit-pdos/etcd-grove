/-
The trust boundary: `(*traceutil.Trace).LogWithStepThreshold` (unit P1b, 2026-10-14): etcd code
left names-only. `logInfo` formats the trace's fields and steps with `fmt.Sprintf`'s `%v` (of
`any` values, `time.Duration`s: beyond Perennial's model of `fmt`, which formats predeclared
basic types only), draws `math/rand.Int31`, builds `zap` fields, and merges a subtrace's fields
into its steps' with `append`; then `t.lg.Info` if the logger is not nil. Total: no index is out
of range (every loop is bounded by `len(t.steps)`), every slice it appends to is the trace's.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogWithStepThreshold

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

axiom traceutil.Trace.LogWithStepThreshold.wp_proof :
    traceutil.Trace.LogWithStepThreshold.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
