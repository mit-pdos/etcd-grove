/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_Lease_LeaseRevoke_Handler.lean` (the client lease's stage (c)). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseRevoke_Handler
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.UnaryHandlerLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- The generated handler of `Lease.LeaseRevoke`: decode a `*LeaseRevokeRequest`, call `srv.LeaseRevoke` (directly or
through the interceptor chain, with `info.FullMethod = "/etcdserverpb.Lease/LeaseRevoke"`), as every
generated unary handler (`wp_unaryHandler`; the build checks that this handler's body is
`unaryHandlerImpl` at these arguments). -/
theorem etcdserverpb._Lease_LeaseRevoke_Handler.wp_proof :
    etcdserverpb._Lease_LeaseRevoke_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandler etcdserverpb._Lease_LeaseRevoke_Handler etcdserverpb.LeaseServer.ty
    etcdserverpb.LeaseRevokeRequest.ty etcdserverpb.LeaseRevokeResponse.ty go!"LeaseRevoke" go!"/etcdserverpb.Lease/LeaseRevoke"

end proof

end EtcdGrove
end Perennial
