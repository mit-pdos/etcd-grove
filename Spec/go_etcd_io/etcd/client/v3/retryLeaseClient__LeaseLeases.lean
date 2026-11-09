/-
`(*clientv3.retryLeaseClient).LeaseLeases` (`client/v3/retry.go`).

Users: `lessor.*` (through `remoteLeaseAt`, `retryLeaseHandle_remoteLeaseAt`).

Proof sketch: appends `withRepeatablePolicy()` (`callOptsOk_append`: a repeatable slice) and calls
`rlc.lc`, the stub over `connOk` (2a/3h): the update persistent, as `RemoteCallTriple` asks of a
repeatable RPC.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/retryLeaseClient__LeaseLeases.lean`: restated over the wire contract; the update persistent (the old `LeaseGrant`, `LeaseRevoke` specs took an exclusive one, unsound against the resend).

verify-round: per member (A2-provability L2): with the client frozen at `ep` (`clientVia c`, the
`RemoteCallTriple`'s `V`), the answer's `viaFact` (the member's lessor view): the stub's connection
is `c.conn`, which reaches `ep` alone (`clientVia_conn`), and `uiOk_call`/`AttemptTriple` give the
fact from the member that answered.

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

/-- `r.LeaseLeases`: the wire contract at its request. -/
def retryLeaseClient.LeaseLeases.spec : Prop :=
  ∀ (r c : Loc) (γ : Cluster) (who : Principal) ,
  RemoteCallTriple (fun s => r @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty @!! s)
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryLeaseHandle r c γ who ∗ clientReady c) γ who .leaseLeases
    (clientVia c)

end spec

end ClientV3
end EtcdGrove
end Perennial
