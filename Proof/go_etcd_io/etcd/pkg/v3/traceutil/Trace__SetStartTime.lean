/-
The trust boundary: `traceutil.Trace.SetStartTime` (a trace's bookkeeping (no effect the model sees); the trace's fields are outside the model).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__SetStartTime

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom traceutil.Trace.SetStartTime.wp_proof : traceutil.Trace.SetStartTime.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
