/-
authN's results (`examples/etcd/authN/authN.go`; `notes/authN-plan.md`, 2026-11-15), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`authN_Main`** (`MainLinked.lean`'s `etcd_authN.wp_Main`): `Main(k)` -- `k` members with the simple
  token provider, then authkv's run across them (`run`) -- does not panic and returns `Ok`, `Failed` or
  `WatchEnded` (`Spec/.../authN/Main.lean`), for `1 ≤ k ≤ 1000`.

**The cluster token.** The program's token is `authN-133`, which appears only in the program and its premises
(the members' configurations in `etcd_authN.premises`): the first `authN-<i>` at which putgetN's `BootFacts`
premise (the member ids' 16 low bits distinct and not `0`) holds for every `k ≤ 300` and across the
clusters of `examples/etcd/all`; `TestMemberIDs` (`examples/etcd/authN/authN_test.go`) checks it for every
`k ≤ 300`, from the ids etcd computes, without starting a cluster. Until 2026-11-21 the token was `authN-1286`, checked for every `k ≤ 1000`; the theorem's `k ≤ 1000`
stays (its proof needs only the ports' bound), but its premise `BootFacts` is checked only for `k ≤ 300`: above,
it may be false of the real ids, and the theorem then says nothing.

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_authN_safe` (with its `_adequate` and `_robust` forms, `Adequacy.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the
`TopLevelRobustness.lean` pair) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_authN.wp_Main`). -/
theorem authN_Main [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_authN.Main.spec (GF := GF) (hG := hG) :=
  etcd_authN.wp_Main

end results

#print axioms authN_Main

end EtcdGrove
end Perennial
