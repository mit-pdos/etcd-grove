/-
`clientv3.toLeaseTimeToLiveRequest` (`client/v3/op.go`).

Users: `lessor.TimeToLive` (1c).

Proof sketch: `LeaseOp.applyOpts.spec` on a fresh `LeaseOp{id}`; a fresh request.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/toLeaseTimeToLiveRequest.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `toLeaseTimeToLiveRequest(id, opts...)`: a fresh `LeaseTimeToLiveRequest` of `id`, `Keys` as the
options set it. -/
def toLeaseTimeToLiveRequest.spec : Prop :=
  ∀ (id : w64) (sl : GoSlice) (gs : List (Bool → Bool)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ leaseOptsAt sl gs }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.toLeaseTimeToLiveRequest)) (Val #id)) (Val #sl))
  {{ (p : Loc), RET #p; leaseOptsAt sl gs ∗
      protoRest go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveRequest p (DFrac.own 1) ∗
      p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveRequest, go!"ID"] ↦ id ∗
      p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveRequest, go!"Keys"] ↦ gs.foldl (fun b g => g b) false }}

end spec

end ClientV3
end EtcdGrove
end Perennial
