/-
The trust boundary: `mvcc.ReportEventReceived` (`metrics.go`, names-only: two prometheus metric
updates; D19j, 2026-10-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived

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

axiom mvcc.ReportEventReceived.wp_proof : mvcc.ReportEventReceived.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
