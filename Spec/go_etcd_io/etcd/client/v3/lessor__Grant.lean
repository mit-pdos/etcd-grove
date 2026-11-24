/-
`(*clientv3.lessor).Grant(ctx, ttl)` (`client/v3/lease.go`; item 1, the client lease). Lean-first
(no Rocq counterpart).
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

/-- `l.Grant(ctx, ttl)` on a `*lessor` over a connection to `addr` (`lessorRemoteAt`), for a spec
`Spec` registered for `LeaseGrant` and the caller's `Q`: the request `{TTL: ttl}` through the retry
lease client; on success a new `*LeaseGrantResponse` whose header, `ID` and `TTL` are the reply's
(`resp.GetHeader()`; read-only) with `Q` of the reply; otherwise `nil` and `ContextError(ctx, err)`,
a client error grpc's `status` accepts. (Auth-lease S4, Freeze §2.2) Over the connection `conn` (`lessorRemoteAtC`), metadata-indexed: the
spec at every metadata an attempt may deliver (`attemptPre`); the old form is the new one at
`GrpcSpec.md` (`attemptPre_md`, `isGrpcRpcs_md`, `lessorRemoteAt_conn`). -/
abbrev lessor.Grant.spec : Prop :=
  ∀ (l conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse)
    (Q : LeaseGrantRespM → IProp GF) (ctx : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
    (ttl : w64),
  {{ levelTok 0 ∗ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorRemoteAtC l conn addr ∗
      isGrpcRpcsMd addr go!"/etcdserverpb.Lease/LeaseGrant" Spec ∗
      metadata.outMD ctx om ∗ □ ▷ attemptPre conn om Spec (ttl, W64 0) Q ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : LeaseGrantRespM) (h : Loc),
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ResponseHeader" resp ↦□ h ∗
        hdrFull h m.hdr ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err)) }}

end spec

end EtcdGrove
end Perennial
