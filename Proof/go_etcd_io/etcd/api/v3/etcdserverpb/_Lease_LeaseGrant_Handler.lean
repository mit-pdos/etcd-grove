/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_Lease_LeaseGrant_Handler.lean` (the client lease's stage (c)). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseGrant_Handler
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

/-- The generated handler of `Lease.LeaseGrant`: decode a `*LeaseGrantRequest`, call `srv.LeaseGrant` (directly or
through the interceptor chain, with `info.FullMethod = "/etcdserverpb.Lease/LeaseGrant"`), as every
generated unary handler (`wp_unaryHandler`; the build checks that this handler's body is
`unaryHandlerImpl` at these arguments). -/
theorem etcdserverpb._Lease_LeaseGrant_Handler.wp_proof :
    etcdserverpb._Lease_LeaseGrant_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandler etcdserverpb._Lease_LeaseGrant_Handler etcdserverpb.LeaseServer.ty
    etcdserverpb.LeaseGrantRequest.ty etcdserverpb.LeaseGrantResponse.ty go!"LeaseGrant" go!"/etcdserverpb.Lease/LeaseGrant"

end proof

end EtcdGrove
end Perennial
