/-
`(*clientv3.lessor).Leases(ctx)` (`client/v3/lease.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
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

/-- `l.Leases(ctx)` on a `*lessor` over a connection to `addr` (`lessorRemoteAt`), for a spec `Spec`
registered for `LeaseLeases` and the caller's `Q`: an empty request through the retry lease client;
on success a new `*LeaseLeasesResponse` whose header is the reply's (`resp.GetHeader()`; read-only)
and whose `Leases` is a new slice (owned) of a `LeaseStatus` for each of the reply's IDs, in order,
with `Q` of the reply; otherwise `nil` and `ContextError(ctx, err)` (as `lessor.Grant.spec`). -/
abbrev lessor.Leases.spec : Prop :=
  ∀ (l : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse)
    (Q : LeaseLeasesRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorRemoteAt l addr ∗
      isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseLeases" Spec ∗ □ ▷ Spec () Q ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : LeaseLeasesRespM) (h : Loc) (sl : GoSlice),
        structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"ResponseHeader" resp ↦□ h ∗
        hdrFull h m.hdr ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
        sl ↦* (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err) }}

end spec

end EtcdGrove
end Perennial
