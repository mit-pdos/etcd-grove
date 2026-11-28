/-
txnlinfaultsN's results (`examples/etcd/txnlinfaultsN/txnlinfaultsN.go`; `notes/txnlinfaultsN-plan.md`,
2026-11-15), restated, with the trust base of each printed in the build log (`#print axioms`). Lean-first
(no Rocq counterpart).

* **`txnlinfaultsN_Main`** (`MainLinked.lean`): `Main(k, clients, ops, sched)` -- `k` etcd members started in
  process with the generic start (`etcdstart.Members`, `etcdstart.StartMembers`, partition's snapshot
  settings `SnapCount = SnapCatchUp = 1`), each member's gRPC server on its client address
  (`127.0.0.1:27000+i`) behind a copy of etcd's test bridge (`127.0.0.1:28000+i`), `k` clients each of all
  `k` bridges (failover, D27), the partitioner forked on the schedule (`cluster3.Partitioner`: the links
  between members cut and mended with etcd's own `CutPeer`/`MendPeer`, both directions; each member's
  bridge blackholed, unblackholed or its connections dropped; a step naming a member index `≥ k` does
  nothing), partition's `Check` (txnlin's workload: gets, ranges, puts, deletes and transactions, each
  through a client picked at random, checked by porcupine against txnlin's model), and a panic if
  porcupine answers `Illegal` -- does not panic and returns `Ok` or `Unknown`, **for every schedule** and
  every member count `1 ≤ k ≤ 1000` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlinfaultsN/Main.lean`).

**The cluster token.** The program's token is `txnlinfaultsN-12748`, which appears only in the program and its
premises (the members' configurations in `etcd_txnlinfaultsN.premises`). etcd computes each member's id
from its peer URL and the token, and `BootFacts` (putgetN's) requires the ids' 16 low bits distinct and not
`0` (etcd's request and lease ids carry them as the member's prefix). For a token chosen at random that
fails for some `k ≤ 1000` (the birthday bound of 16 bits), which would make the theorem vacuous at those `k`;
putgetN's token does not carry over, since the peer URLs differ. `txnlinfaultsN-12748` is the first
`txnlinfaultsN-<i>` at which the premise holds for every `k ≤ 1000` (member `i`'s id is the same in every
cluster of more than `i` members, so the check at `k = 1000` covers every `k`) and across the clusters of
`examples/etcd/all` (the others at `k ≤ 300`; until 2026-11-21 `txnlinfaultsN-6255`); `TestMemberIDs`
(`examples/etcd/txnlinfaultsN/txnlinfaultsN_test.go`) checks it for every `k`, from the ids etcd computes,
without starting a cluster.

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_txnlinfaultsN_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]
variable [NaInvG GF]

/-- **`Main(k, clients, ops, sched)` does not panic, for every schedule** (`MainLinked.lean`'s
`etcd_txnlinfaultsN.wp_Main`). -/
theorem txnlinfaultsN_Main :
    etcd_txnlinfaultsN.Main.spec (GF := GF) (hG := hG) :=
  etcd_txnlinfaultsN.wp_Main

end results

#print axioms txnlinfaultsN_Main

end EtcdGrove
end Perennial
