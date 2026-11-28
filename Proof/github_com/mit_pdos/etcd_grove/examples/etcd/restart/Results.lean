/-
**restart3's results** (restart3 C4, 2026-11-15): `restart3_Main` (`MainLinked.lean`'s `wp_Main`) and the
closed theorem `etcd_restart3_safe` (statement approved by the user, 2026-11-15, via etcd-grove-81), with
`#print axioms` of each.

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_restart3_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_restart.wp_Main`). -/
theorem restart3_Main :
    etcd_restart.Main.spec (GF := GF) (hG := hG) :=
  etcd_restart.wp_Main

end results

#print axioms restart3_Main

end EtcdGrove
end Perennial
