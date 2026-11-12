/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_Lease_LeaseLeases_Handler.lean` (the client lease's stage (c)). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.UnaryHandlerLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- The generated handler of `Lease.LeaseLeases`: decode a `*LeaseLeasesRequest`, call `srv.LeaseLeases` (directly or
through the interceptor chain, with `info.FullMethod = "/etcdserverpb.Lease/LeaseLeases"`), as every
generated unary handler (`wp_unaryHandler`; the build checks that this handler's body is
`unaryHandlerImpl` at these arguments). -/
theorem etcdserverpb._Lease_LeaseLeases_Handler.wp_proof :
    etcdserverpb._Lease_LeaseLeases_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandler etcdserverpb._Lease_LeaseLeases_Handler etcdserverpb.LeaseServer.ty
    etcdserverpb.LeaseLeasesRequest.ty etcdserverpb.LeaseLeasesResponse.ty go!"LeaseLeases" go!"/etcdserverpb.Lease/LeaseLeases"

end proof

end EtcdGrove
end Perennial
