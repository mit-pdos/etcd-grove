/-
`(*etcdserverpb.leaseClient).LeaseGrant(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the
generated Lease stub; item 1, the client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.LeaseGrant(ctx, in, opts...)` on a stub on a connection to the server at `addr`
(`leaseStubAt`), for a spec `Spec` the server registered for the method and the caller's `Φ`:
`Invoke` of `"/etcdserverpb.Lease/LeaseGrant"` with `grpc.StaticMethod()` before the options,
into a new `*LeaseGrantResponse`: the call's answer (`leaseGrantCallOut`); the request comes back. -/
abbrev leaseClient.LeaseGrant.spec : Prop :=
  ∀ (lc conn : Loc) (addr : GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse)
    (Φ : LeaseGrantRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.LeaseGrantRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ leaseStubAt lc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant" Spec ∗
      □ ▷ Spec (req.TTL', req.ID') Φ ∗ ctxOk ctx cd ∗ inp ↦ req ∗ opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (lc @!! go.GoType.PointerType etcdserverpb.leaseClient.ty @!! go!"LeaseGrant"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.LeaseGrantRequest, inp ↦ req') ∗ leaseGrantCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
