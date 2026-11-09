/-
`(*clientv3.lessor).Leases` (`client/v3/lease.go`).

Users: `examples/etcd/{lease,leasegrant,leaseexpiry,leasecatchup}` (an id listed once; through one
member, a granted id listed: `LeaseRead.Triple`'s per-member view), snippets `clientv3lease/reads.go`
(`ReqLeasesNoDup`), `clientv3lease/member.go` (`ReqGrantThenListOneMember`, `ReqGoneNotListed`).

Proof sketch: `l.remote.LeaseLeases` (repeatable: persistent), a fresh `[]LeaseStatus` of the reply's
ids in order (a loop over `resp.Leases`: 3h's unfold of `replyOwn _ (.leaseLeases ids)`); `ContextError`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__Leases.lean`: restated over the model.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `l.Leases(ctx)`: the ids a lessor lists, linearized by the caller's persistent update. -/
def lessor.Leases.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal),
  Lease.LeasesTriple (fun s => l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! s) (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l) iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
