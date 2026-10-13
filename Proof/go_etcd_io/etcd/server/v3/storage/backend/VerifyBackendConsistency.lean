/-
The trust boundary: `backend.VerifyBackendConsistency` (names-only: verification code, enabled by `ETCD_VERIFY`, which
checks the backend's consistency and panics on a violation; as `verify.Verify`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.VerifyBackendConsistency

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom backend.VerifyBackendConsistency.wp_proof : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
