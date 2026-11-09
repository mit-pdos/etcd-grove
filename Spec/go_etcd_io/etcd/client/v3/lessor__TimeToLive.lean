/-
`(*clientv3.lessor).TimeToLive` (`client/v3/lease.go`).

Users: `examples/etcd/{lease,leaseexpiry}` (`TTL == -1 && GrantedTTL == 0`: gone), snippet
`clientv3lease/reads.go` (`ReqTimeToLiveNotFound`, `ReqTimeToLiveKeys`).

Proof sketch: `toLeaseTimeToLiveRequest(id, opts...)` (W0's spec: `ID`, `Keys` the options' fold),
`l.remote.LeaseTimeToLive` (repeatable: persistent update; the handler maps `ErrLeaseNotFound` to a
reply with `TTL = -1`: `leaseTTLReply`), copies the reply's fields into a fresh
`LeaseTimeToLiveResponse`; `ContextError` on an error.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__TimeToLive.lean` (one server's lessor):
restated over the model (a lessor behind or deposed: `leaseStep`).

verify-round (A2-provability L2): the per-member clause (`via`) now has a source: `leaseViaPre`'s
`leaseOf v c ∗ clientVia c ep` gives, through `lessorHandle`'s realization, `remoteVia` of the remote
(`NewLeaseFromLeaseClient`'s premise), and `remoteLeaseAt_call` at `V = remoteVia remote` gives the
answer's `viaFact` (from 2a's `AttemptTriple` through `uiOk_call`); a lease read's fact holds for an
answer of the lessor (`leaseAnsRes`), not for a refusal.

re-review N1, recheck RR-1: the per-member clause holds for `TimeToLive` only given W0's `soleMember γ`
(a gated row of `viaFact`; introduced by 2e's `soleMember_intro`: one initial member, no URL set
ever reserved, so no member is ever added): a follower forwards it to the leader
(`v3_server.go:636-676`).

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

/-- `l.TimeToLive(ctx, id, opts...)`: `.leaseTimeToLive id keys` (`keys`: `WithAttachedKeys`)
linearized by the caller's persistent update; a lease the lessor does not know is the reply
`TTL = -1`. -/
def lessor.TimeToLive.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal),
  Lease.TimeToLiveTriple (fun s => l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! s) (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l) iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
