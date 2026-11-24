/-
**restartN's results** (`notes/restartN-plan.md`, 2026-11-15): `restartN_Main` (`MainLinked.lean`'s `wp_Main`)
and the closed theorem `etcd_restartN_safe` (statement approved by the user, 2026-11-15, via etcd-grove-81, with
`3 ≤ k ≤ 1000`; `notes/restartN-draft.md`), with `#print axioms` of each.

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_restartN_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_restartN.wp_Main`), for every `k ≤ 1000`. -/
theorem restartN_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions] :
    etcd_restartN.Main.spec (GF := GF) (hG := hG) :=
  etcd_restartN.wp_Main

end results

#print axioms restartN_Main

end EtcdGrove
end Perennial
