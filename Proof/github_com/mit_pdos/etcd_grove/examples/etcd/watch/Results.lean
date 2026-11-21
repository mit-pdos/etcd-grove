/-
The watch example's results (`examples/etcd/watch/etcd_watch.go`; D23), restated, with the trust base
of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`watchkv_Main`** (`Link.lean`'s `etcd_watch.wp_Main`): `Main(nw, nops)` -- the Puts picked, one
  etcd member started in process, a client with etcd's default configuration, a prefix watch from revision `1`, `nw`
  writers, the watch read up to the highest successful revision, and a check that panics unless
  the watched events are exactly the writes -- does not panic and returns `Ok`, `Failed` or
  `WatchEnded`. From `isPkgInit watchkv`, the right to listen on `127.0.0.1:23872`, the main
  thread's token and `Main`'s named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/watch/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_watch_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.watch.Link

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.watch.Assumptions]

/-- **`Main` does not panic** (`Link.lean`'s `etcd_watch.wp_Main`). -/
theorem watchkv_Main [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_watch.Main.spec (GF := GF) (hG := hG) :=
  etcd_watch.wp_Main

end results

#print axioms watchkv_Main

end EtcdGrove
end Perennial
