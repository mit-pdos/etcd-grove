/-
`(*etcdserverpb.leaseClient).LeaseTimeToLive(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the
generated Lease stub; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.LeaseTimeToLive(ctx, in, opts...)` on a stub on a connection to the server at `addr`
(`leaseStubAt`), for a spec `Spec` the server registered for the method and the caller's `Φ`:
`Invoke` of `"/etcdserverpb.Lease/LeaseTimeToLive"` with `grpc.StaticMethod()` before the options,
into a new `*LeaseTimeToLiveResponse`: the call's answer (`leaseTTLCallOut`); the request comes back. The
request has no unknown fields (a struct literal; 2026-10-30, the wire model's bound,
`ProtoMsg.wireLen`). -/
abbrev leaseClient.LeaseTimeToLive.spec : Prop :=
  ∀ (lc conn : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse)
    (Φ : LeaseTTLRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.LeaseTimeToLiveRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ leaseStubAt lc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseTimeToLive" Spec ∗
      □ ▷ Spec (req.ID', req.Keys') Φ ∗ ctxOk ctx cd ∗ inp ↦ req ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      ⌜req.unknownFields' = slice.nil⌝ }}
    (App (App (App (Val (lc @!! go.GoType.PointerType etcdserverpb.leaseClient.ty @!! go!"LeaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.LeaseTimeToLiveRequest, inp ↦ req') ∗ leaseTTLCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
