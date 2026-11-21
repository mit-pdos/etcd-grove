/-
putget3's results (`examples/etcd/putget3/etcd_putget3.go`; D21 stage M5, 2026-10-19), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`putget3_Main`** (`MainLinked.lean`): `Main` -- three etcd members started in process
  (`startMember`: `NewServer`, the raft handler served on the member's peer listener
  (`RaftHandler`, `http.Serve`), `Start`), the first's gRPC server listening at `127.0.0.1:23791`, a
  client, a `Put` of `k` with value `v`, a `Get` of `k`, and a panic unless the `Get` returned `v`
  -- returns: it does not panic (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putget3/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_putget3_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_putget3.wp_Main`). -/
theorem putget3_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_putget3.Main.spec (GF := GF) (hG := hG) :=
  etcd_putget3.wp_Main

end results

#print axioms putget3_Main

end EtcdGrove
end Perennial
