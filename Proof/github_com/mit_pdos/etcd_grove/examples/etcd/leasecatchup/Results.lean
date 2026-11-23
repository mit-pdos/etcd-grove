/-
The multi-member lease example's results (`examples/etcd/leasecatchup/leasecatchup.go`; lease-mono3
step 1, 2026-11-06, `notes/lease-mono3-plan.md`), restated, with the trust base of each printed in
the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`leasecatchup_Main`** (`MainLinked.lean`): `Main` -- three etcd members started in process in
  the monotone lease mode (`cluster3.StartCluster`), a client of member 3's bridge and one of member
  1's, a lease granted through member 3, member 3 cut off while fillers are granted through member 1,
  the links mended, member 3's listing polled until it lists the last filler, and a panic unless it
  lists the first lease too -- returns: it does not panic. From `isPkgInit leasecatchup`, the
  cluster's start bundle, the main thread's token and the cluster's named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_leasecatchup_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_leasecatchup.wp_Main`). -/
theorem leasecatchup_Main [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leasecatchup.Main.spec (GF := GF) (hG := hG) :=
  etcd_leasecatchup.wp_Main

end results

#print axioms leasecatchup_Main

end EtcdGrove
end Perennial
