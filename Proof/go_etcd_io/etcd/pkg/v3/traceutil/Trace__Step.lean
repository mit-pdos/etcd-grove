/-
The trust boundary: `(*traceutil.Trace).Step` (names-only; tracing is bookkeeping for logs).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom traceutil.Trace.Step.wp_proof : traceutil.Trace.Step.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
