/-
`Main()` (`examples/etcd/leaseexpiry/leaseexpiry.go`; the closed lease-expiry example, 2026-11-04,
`notes/lease-expiry-plan.md`, Part E): one etcd member started in process, a client connected to
it, its `Grant(1)`, `TimeToLive` polled until the lease is not found (`TTL = -1 ∧ GrantedTTL = 0`),
then `Leases()`, and a panic if the listing has the lease. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23976` (`netAddrFree`), the main thread's token and `Main`'s named premises
(`etcd_leaseexpiry.premises`, `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiry/Defs.lean`),
`Main()` returns: it does not panic. **No premise about time**: unlike `leasegrant`'s, there is no
`lease.leasesNoExpiry`; the member's lessor is revocable (the lease mode `.revocable`) and its
expiry loop revokes the lease. Why the listing cannot have it: `TimeToLive`'s not-found answer says
the lease was absent from the lessor's history at an index after its grant (the single-member,
first-incarnation row of the trusted `leaseTimeToLive`), and a lease id is granted once (generated
ids only, the plan's E3), so it stays absent at every later index, among them the listing's.

**The pure premises:** as `leasegrant`'s (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasegrant/Main.lean`)
but `lease.leasesNoExpiry`: the member id and bootstrap log Go computes (`BootFacts`); the thread and
time-receipt bounds; the write budget; the named workload and effect premises of the server's
construction (`authRecordsFit`, `apply.backendUnderQuota`, `grpcRepliesFit`,
`storage.diskOk`); the deployment's peers answering the lease handler's path (`leasePeersOk`); Go's
method sets of the gRPC service values and `errors.As`'s target.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiry

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry),
  BootFacts id ctxs boot →
  -- (revoke-open, 2026-11-06) the revocation's goroutines' levels 0–3 (`srvRevokeLevels`)
  threadBound GF ≤ 2 ^ 28 → srvRevokeLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 →
    receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry ∗
      -- (2026-11-05, hub step 7) the member's start bundle: its WAL directory fresh and the right
      -- to listen on its client address (`netAddrFree`, which program start gives once: D19d)
      etcdstart.memberStartRes (GF := GF) go!"leaseexpiry" ⟨none, some go!"127.0.0.1:23976"⟩ ∗
      threadTok ∗ premises N id ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_leaseexpiry
end EtcdGrove
end Perennial
