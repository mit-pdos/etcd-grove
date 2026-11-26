/-
The KV-workload linearizability instance's results (`examples/etcd/txnlin/etcd_txnlin.go`; linkv-txn
stage G), restated, with the trust base of each printed in the build log (`#print axioms`).
Lean-first (no Rocq counterpart).

* **`linkvtxn_Main`** (`Link.lean`'s `etcd_txnlin.wp_Main`): `Main(clients, ops)` -- one etcd member
  started in process, a client with etcd's default configuration, `Check(cli, clients, ops, 0)`
  (`lintest.Run` with the model of etcd's KV, `Apply` over the client: gets, lists, puts, deletes,
  transactions; porcupine's checker), and a panic if porcupine answers `Illegal` -- does not panic
  and returns `Ok` or `Unknown`. From `isPkgInit linkvtxn`, the right to listen on
  `127.0.0.1:23796`, the main thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlin/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_txnlin_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Link

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic** (`Link.lean`'s `etcd_txnlin.wp_Main`). -/
theorem linkvtxn_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    :
    etcd_txnlin.Main.spec (GF := GF) (hG := hG) :=
  etcd_txnlin.wp_Main

end results

#print axioms linkvtxn_Main

end EtcdGrove
end Perennial
