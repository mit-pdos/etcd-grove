/-
putgetN's results (`examples/etcd/putgetN/putgetN.go`; the clusterN Scope, `notes/clusterN-scope.md`,
2026-11-15), restated, with the trust base of each printed in the build log (`#print axioms`).
Lean-first (no Rocq counterpart).

* **`putgetN_Main`** (`MainLinked.lean`): `Main(k)` -- `k` etcd members started in process
  (`etcdstart.Members`, `etcdstart.StartMembers`: `NewServer`, the raft handler served on the member's
  peer listener, `Start`), member `0`'s gRPC server listening at `127.0.0.1:25000`, a client, a `Put`
  of `k` with value `v`, a `Get` of `k`, and a panic unless the `Get` returned `v` -- returns: it does
  not panic (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putgetN/Main.lean`), for `1 ≤ k ≤ 1000`.

**The cluster token.** The program's token is `putgetN-1405`, which appears only in the program and its
premises (the members' configurations in `etcd_putgetN.premises`). etcd computes each member's id from its
peer URL and the token, and `BootFacts` (as putget3's) requires the ids' 16 low bits distinct and not `0`
(etcd's request and lease ids carry them as the member's prefix). For a token chosen at random that fails
for some `k ≤ 1000` (the birthday bound of 16 bits: at the token `putgetN` first at `k = 214`), which would
make the theorem vacuous at those `k`. `putgetN-1405` is the first `putgetN-<i>` at which the premise holds
for every `k ≤ 1000`; `TestMemberIDs` (`examples/etcd/putgetN/putgetN_test.go`) checks it for every `k`,
from the ids etcd computes, without starting a cluster.

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_putgetN_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_putgetN.wp_Main`). -/
theorem putgetN_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_putgetN.Main.spec (GF := GF) (hG := hG) :=
  etcd_putgetN.wp_Main

end results

#print axioms putgetN_Main

end EtcdGrove
end Perennial
