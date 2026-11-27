/-
The cache watch example's results (`examples/etcd/cache/etcd_cache.go`), restated, with the trust base
of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`cachekv_Main`** (`Link.lean`'s `etcd_cache.wp_Main`): `Main(nw, nops)` -- the Puts picked, one
  etcd member started in process (since 2026-11-02 with the auto-compactor on, periodic mode
  at 10ms: a compaction of the cache's watch makes the cache re-list), a client with etcd's default configuration, a cache of the prefix over it, the cache's
  watch of the prefix from revision `2`, `nw` writers, the watch read up to the highest successful
  revision, a progress notification of the watch and a check that panics if it is past the last
  event, a check that panics unless the watched events are exactly the writes, then the cache's
  `Get` of the prefix at that revision and a check that panics unless it answers each key's last
  watched value (`checkGet`) -- does not panic and returns `Ok`, `Failed`, `WatchEnded` or
  `GetFailed`. From `isPkgInit cachekv`, the right to listen
  on `127.0.0.1:23873`, the main thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_cache_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Link

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]

/-- **`Main` does not panic** (`Link.lean`'s `etcd_cache.wp_Main`). -/
theorem cachekv_Main
    [go_etcd_io.etcd.cache.v3.Assumptions] :
    etcd_cache.Main.spec (GF := GF) (hG := hG) :=
  etcd_cache.wp_Main

end results

#print axioms cachekv_Main

end EtcdGrove
end Perennial
