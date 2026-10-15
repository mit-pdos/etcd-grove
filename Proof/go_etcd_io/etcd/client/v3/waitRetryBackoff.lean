/-
**Trust boundary**: `waitRetryBackoff` (timers) returns `nil` or a gRPC status error (an axiom; see `Spec/go_etcd_io/etcd/client/v3/waitRetryBackoff.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.waitRetryBackoff

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary**: `waitRetryBackoff` (timers) returns `nil` or a gRPC status error. -/
axiom waitRetryBackoff.wp_proof : waitRetryBackoff.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
