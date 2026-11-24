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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.LeaseGrant(ctx, in, opts...)` on a stub on a connection to the server at `addr`
(`leaseStubAt`), for a spec `Spec` the server registered for the method and the caller's `Φ`:
`Invoke` of `"/etcdserverpb.Lease/LeaseGrant"` with `grpc.StaticMethod()` before the options,
into a new `*LeaseGrantResponse`: the call's answer (`leaseGrantCallOut`); the request comes back. The
request has no unknown fields (a struct literal; 2026-10-30, the wire model's bound,
`ProtoMsg.wireLen`). (Auth-lease S4, Freeze §2.3) Metadata-indexed: the spec `Spec` at every metadata an attempt may deliver
(`attemptPre`, as `kVClient.Put`'s; a plain spec is `GrpcSpec.md`); persistent, since the call may be
retried. -/
abbrev leaseClient.LeaseGrant.spec : Prop :=
  ∀ (lc conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse)
    (Φ : LeaseGrantRespM → IProp GF) (ctx : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.LeaseGrantRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ levelTok 0 ∗ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ leaseStubAt lc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcsMd addr go!"/etcdserverpb.Lease/LeaseGrant" Spec ∗
      metadata.outMD ctx om ∗ □ ▷ attemptPre conn om Spec (req.TTL', req.ID') Φ ∗ ctxOk ctx cd ∗ inp ↦ req ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      ⌜req.unknownFields' = slice.nil⌝) }}
    (App (App (App (Val (lc @!! go.GoType.PointerType etcdserverpb.leaseClient.ty @!! go!"LeaseGrant"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((∃ req' : etcdserverpb.LeaseGrantRequest, inp ↦ req') ∗ leaseGrantCallOut Φ resp err) }}

end spec

end EtcdGrove
end Perennial
