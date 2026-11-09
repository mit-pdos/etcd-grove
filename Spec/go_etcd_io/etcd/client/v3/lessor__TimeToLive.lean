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
  ∀ (l : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (id : w64) (opts : GoSlice)
    (gs : List (Bool → Bool)),
  CallTriple (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"TimeToLive")) (Val #ctx)) (Val #id)) (Val #opts))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ leaseOptsAt opts gs) (leaseOptsAt opts gs) γ who
    (.leaseTimeToLive (sint.Z id) (gs.foldl (fun b g => g b) false)) true (leaseTTLReply (sint.Z id))

end spec

end ClientV3
end EtcdGrove
end Perennial
