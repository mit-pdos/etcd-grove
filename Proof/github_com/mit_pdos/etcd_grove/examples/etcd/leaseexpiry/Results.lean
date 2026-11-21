/-
The closed lease-expiry example's results (`examples/etcd/leaseexpiry/leaseexpiry.go`; 2026-11-05,
`notes/lease-expiry-plan.md`), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`leaseexpiry_Main`** (`MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23976`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), its `Grant(1)`,
  `TimeToLive` polled until the lease is not found, then `Leases()`, and a panic if the listing has
  the lease
  -- returns: it does not panic. From
  `isPkgInit leaseexpiry`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiry/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_leaseexpiry_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.MainLinked

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_leaseexpiry.wp_Main`). -/
theorem leaseexpiry_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leaseexpiry.Main.spec (GF := GF) (hG := hG) :=
  etcd_leaseexpiry.wp_Main

end results

#print axioms leaseexpiry_Main

end EtcdGrove
end Perennial
