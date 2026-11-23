/-
auth3's results (`examples/etcd/auth3/auth3.go`; the auth3 Scope's A1, `notes/auth3-scope.md`, and since
2026-11-14 its A2: every member serving, each principal through its own member, after a barrier),
restated, with the trust base of each printed in the build log (`#print axioms`). Lean-first (no
Rocq counterpart).

* **`auth3_Main`** (`MainLinked.lean`'s `etcd_auth3.wp_Main`): `Main()` -- three members with the
  simple token provider, then authkv's run across them (`run`) -- does not panic and returns `Ok`,
  `Failed` or `WatchEnded` (`Spec/.../auth3/Main.lean`).

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_auth3_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_auth3.wp_Main`). -/
theorem auth3_Main [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [EtcdGrove.ErrorStringLeaf] :
    etcd_auth3.Main.spec (GF := GF) (hG := hG) :=
  etcd_auth3.wp_Main

end results

#print axioms auth3_Main

end EtcdGrove
end Perennial
