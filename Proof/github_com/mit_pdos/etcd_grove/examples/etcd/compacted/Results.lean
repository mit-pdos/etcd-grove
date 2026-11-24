/-
**`putgetc`** (M2, 2026-10-27, `notes/m2-plan.md`): putget's file, for putget with the
auto-compactor on (`etcdstart.StartPeriodicServer`, periodic mode, period 10ms, since 2026-11-02;
until then `etcdstart.StartCompactingServer`, revision mode, retention 1); putget's history
below is the original's.

The adequacy example's results (`examples/etcd/compacted/etcd_compacted.go`; item 9), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`putgetc_Main`** (stage 2, 2026-10-18; `MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23791`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), a `Put` of `k` with value `v`, a
  `Get` of `k`, and a panic unless the `Get` returned `v` -- returns: it does not panic. From
  `isPkgInit putgetc`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/compacted/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_compacted_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.compacted.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.compacted.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_compacted.wp_Main`). -/
theorem putgetc_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_compacted.Main.spec (GF := GF) (hG := hG) :=
  etcd_compacted.wp_Main

end results

#print axioms putgetc_Main

end EtcdGrove
end Perennial
