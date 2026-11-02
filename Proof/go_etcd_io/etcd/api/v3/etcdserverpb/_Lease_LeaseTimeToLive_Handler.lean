/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_Lease_LeaseTimeToLive_Handler.lean` (the client lease's stage (c)). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
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

/-- The generated handler of `Lease.LeaseTimeToLive`: decode a `*LeaseTimeToLiveRequest`, call `srv.LeaseTimeToLive` (directly or
through the interceptor chain, with `info.FullMethod = "/etcdserverpb.Lease/LeaseTimeToLive"`), as every
generated unary handler (`wp_unaryHandler`; the build checks that this handler's body is
`unaryHandlerImpl` at these arguments). -/
theorem etcdserverpb._Lease_LeaseTimeToLive_Handler.wp_proof :
    etcdserverpb._Lease_LeaseTimeToLive_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandler etcdserverpb._Lease_LeaseTimeToLive_Handler etcdserverpb.LeaseServer.ty
    etcdserverpb.LeaseTimeToLiveRequest.ty etcdserverpb.LeaseTimeToLiveResponse.ty go!"LeaseTimeToLive" go!"/etcdserverpb.Lease/LeaseTimeToLive"

end proof

end EtcdGrove
end Perennial
