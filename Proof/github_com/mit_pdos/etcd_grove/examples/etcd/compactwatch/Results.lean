/-
**`compactkv`** (the client's `kv.Compact`, 2026-11-01): putgetc's file, for putgetc under
compaction pressure (`etcdstart.StartCompactingServer`, revision mode, retention 1; five rounds of a
put of the round's key, a client compaction at the revision before it, a get of the key);
putgetc's and putget's history below is the originals'.

The adequacy example's results (`examples/etcd/compactwatch/etcd_compactwatch.go`; item 9), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`compactkv_Main`** (stage 2, 2026-10-18; `MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23794`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), five rounds of a `Put` of the
  round's key with value `v`, a `Compact` at the revision before it and a `Get` of the key, each with
  a panic unless the `Get` returned `v` (since 2026-11-02, the read-side law: at a revision at
  least the `Put`'s), and (C3's watch side, 2026-11-02) a watch from revision `2` whose
  compaction revision plus the retention is at most a later latest `Get`'s
  (`checkCompactRev`) -- returns: it does not panic. From
  `isPkgInit compactkv`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/compactwatch/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_compactwatch_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.compactwatch.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.compactwatch.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_compactwatch.wp_Main`). -/
theorem compactkv_Main :
    etcd_compactwatch.Main.spec (GF := GF) (hG := hG) :=
  etcd_compactwatch.wp_Main

end results

#print axioms compactkv_Main

end EtcdGrove
end Perennial
