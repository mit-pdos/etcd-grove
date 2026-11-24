/-
leaseN's results (`examples/etcd/leaseN/leaseN.go`; `notes/leaseN-plan.md`, 2026-11-16), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`leaseN_Main`** (`MainLinked.lean`): `Main(k)` -- `k` etcd members started in process
  (`etcdstart.Members`, `etcdstart.StartMembers`), every member's gRPC server listening at its client
  address `127.0.0.1:(11000+i)`, and at every member, through a client of that member, `Leases()` and
  `TimeToLive(7)`, with a panic if the listing has a lease twice or the answer is about another lease
  -- returns: it does not panic (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseN/Main.lean`),
  for `1 ≤ k ≤ 1000`.

**The cluster token.** `leaseN-1302`, the first `leaseN-<i>` at which putgetN's `BootFacts` (the ids' 16 low
bits distinct and not `0`) holds for every `k ≤ 300` and across the clusters of `examples/etcd/all`;
`TestMemberIDs` (`examples/etcd/leaseN/leaseN_test.go`) checks it from the ids etcd computes. No member grants a
lease, so the ids' 15 low bits need not be distinct. Until 2026-11-21 the token was `leaseN-2422`, checked for every `k ≤ 1000`; the theorem's `k ≤ 1000`
stays (its proof needs only the ports' bound), but its premise `BootFacts` is checked only for `k ≤ 300`: above,
it may be false of the real ids, and the theorem then says nothing.

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_leaseN_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_leaseN.wp_Main`). -/
theorem leaseN_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leaseN.Main.spec (GF := GF) (hG := hG) :=
  etcd_leaseN.wp_Main

end results

#print axioms leaseN_Main

end EtcdGrove
end Perennial
