/-
`(*lessor).Leases(ctx)` at a member, monotone lease mode, by a client of a member at another machine, at the cluster view: an interim trust-boundary axiom
(`notes/etcd-dist-plan.md` §18.4). The real Go is translated; the cross-machine proof needs #24's S2 client
side, which retires it. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesGrantedDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace view

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **INTERIM: `(*lessor).Leases(ctx)` at a member, monotone lease mode** (trust boundary until #24's S2 client side; see the spec). What it asserts of
clientv3 v3.6 and grpc-go v1.84 (the model) over the net extension.

**Why it is an axiom** (the standing rule's order, as `KV_Put_dist`): the real Go is translated and in one
process it is proved (`lessor.Leases.spec` at `etcdLeaseLeasesSpec γl` (`etcdLeaseLeasesSpecW`), over `Invoke`'s registration); across machines the call goes through grpc's
`Invoke` over the net extension, where no proof establishes the protocols of any bytes and `etcdSvc` has no
law. A Go model with the same behaviour is the grpc model itself (the same gap); a trusted stand-in would
trust more than a contract per function.

**Why it is true.** It is the in-process `lessor.Leases.spec` at `etcdLeaseLeasesSpec γl` (`etcdLeaseLeasesSpecW`) with the registration replaced by `leaseClientAt` (the
address fact at `Γ`), `levelTok 0` lent and returned as there, and the error arm without `clientErr`/
`statusErrOk` (nothing is claimed of a remote call's error):
* *Who answers.* `clientNoProxy`: the client dials the endpoint itself. The endpoint's table is set once by
  the start and answered successfully only by `Serve_dist` at member `mid` (`etcdAddrAt ep Γ mid`); another
  program at the address answers no call successfully (the error arm).
* *Errors, timeouts, retries are the error arm.* `Grant` and `Leases`/`TimeToLive` are retried by clientv3's
  interceptor on `Unavailable` (`isSafeRetryImmutableRPC` for the reads; a retried `Grant` can only grant
  another lease, which the post does not mention); a deadline or a partition returns `err ≠ nil`, no claim.
* *The lessor name.* `Γ.ls mid` is the name the start allocated for member `mid`'s lessor (P-L1:
  `NewServer` takes it from the member's slice and `NewLessor` makes its lessor there; `lease.lessorSlot`), so
  the facts the post gives (`leaseGrantedAt`, `leaseLiveFrom`, `leaseReqIs`, `leaseIdsAt`) are about the
  history of the lessor that answered. `LeaseGrant`/`LeaseLeases` are member-local (`EtcdServer.LeaseGrant`
  replies after the member's own apply of the grant; `LeaseLeases` reads the member's own lessor, no read
  index), hence one endpoint and the member's own name. **Until P-L1 is in, no linked result may use this
  axiom** (the start's `DistView.ofKV` names a constant).

Retired by #24's S2 client side (`etcdSvc` defined, `Invoke` over the net model). The statement does not
change. -/
axiom Lease_LeasesGranted_dist.wp_proof : Lease_LeasesGranted_dist.spec (GF := GF) (hG := hG)

end proof

end view
end etcd_dist
end EtcdGrove
end Perennial
