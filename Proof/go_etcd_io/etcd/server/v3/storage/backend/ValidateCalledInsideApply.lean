/-
The trust boundary: `Spec/go_etcd_io/etcd/server/v3/storage/backend/ValidateCalledInsideApply.lean` (`verify.go`
is names-only; the spec assumes the lock checks are off).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledInsideApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom backend.ValidateCalledInsideApply.wp_proof : backend.ValidateCalledInsideApply.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
