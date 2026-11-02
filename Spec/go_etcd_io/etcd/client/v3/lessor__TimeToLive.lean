/-
`(*clientv3.lessor).TimeToLive(ctx, id, opts...)` (`client/v3/lease.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
Rocq counterpart).
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

/-- `l.TimeToLive(ctx, id, opts...)` on a `*lessor` over a connection to `addr` (`lessorRemoteAt`),
for a spec `Spec` registered for `LeaseTimeToLive` and the caller's `Q`: the request for `id` (its
`Keys` as the options `gs` leave it, `toLeaseTimeToLiveRequest`) through the retry lease client; on
success a new `*LeaseTimeToLiveResponse` whose header, `ID`, `TTL`, `GrantedTTL` are the reply's
(`resp.GetHeader()`; read-only) and whose `Keys` is the reply's slice, with `Q` of the reply;
otherwise `nil` and `ContextError(ctx, err)`, a client error grpc's `status` accepts (as
`lessor.Grant.spec`). -/
abbrev lessor.TimeToLive.spec : Prop :=
  ∀ (l : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse)
    (Q : LeaseTTLRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (id : w64) (sl : GoSlice) (gs : List (Bool → Bool)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorRemoteAt l addr ∗
      isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseTimeToLive" Spec ∗
      □ ▷ Spec (id, leaseKeysFold gs false) Q ∗ leaseOptsAt sl gs ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
        go!"TimeToLive")) (Val #(GoInterface.ok ctx))) (Val #id)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : LeaseTTLRespM) (h : Loc) (ks : GoSlice),
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ResponseHeader" resp ↦□ h ∗
        hdrFull h m.hdr ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"TTL" resp ↦□ m.ttl ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"GrantedTTL" resp ↦□
          m.grantedTtl ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"Keys" resp ↦□ ks ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err) }}

end spec

end EtcdGrove
end Perennial
