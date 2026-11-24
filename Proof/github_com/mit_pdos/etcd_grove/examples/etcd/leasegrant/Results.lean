/-
The closed lease-grant example's results (`examples/etcd/leasegrant/etcd_leasegrant.go`; 2026-11-02,
`notes/lease-grant-plan.md`), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`leasegrant_Main`** (`MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23956`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), its `Grant(600)`
  and `Leases()`, and a panic unless the listing has the lease granted
  -- returns: it does not panic. From
  `isPkgInit leasegrant`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasegrant/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_leasegrant_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_leasegrant.wp_Main`). -/
theorem leasegrant_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leasegrant.Main.spec (GF := GF) (hG := hG) :=
  etcd_leasegrant.wp_Main

end results

#print axioms leasegrant_Main

end EtcdGrove
end Perennial
