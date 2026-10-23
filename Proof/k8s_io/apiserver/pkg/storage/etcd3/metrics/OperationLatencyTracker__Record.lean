/-
The trust boundary of `metrics.OperationLatencyTracker.Record` (see its spec).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.OperationLatencyTracker__Record

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom metrics.OperationLatencyTracker.Record.wp_proof : metrics.OperationLatencyTracker.Record.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
