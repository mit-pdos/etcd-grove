/-
authlease's results (`examples/etcd/authlease/authlease.go`; auth-lease S4, `notes/auth-lease-s4-draft.md`,
2026-11-19), restated, with the trust base of each printed in the build log (`#print axioms`). Lean-first (no
Rocq counterpart).

* **`authlease_Main`** (`MainLinked.lean`'s `etcd_authlease.wp_Main`): `Main(k)` -- `k` members with the simple
  token provider in the revocable lease mode, then the lease checks across them (`run`) -- does not panic and
  returns `Ok` or `Failed` (`Spec/.../authlease/Main.lean`), for `1 ≤ k ≤ 1000`.

**The cluster token.** The program's token is `authlease-1787`, which appears only in the program and its
premises: the first `authlease-<i>` at which putgetN's `BootFacts` premise and `leaseIdsApart` (the member ids'
15 low bits distinct) hold for every `k ≤ 300`, and `BootFacts` across the clusters of `examples/etcd/all`;
`TestMemberIDs` (`examples/etcd/authlease/authlease_test.go`) checks it for every `k ≤ 300`, from the ids etcd
computes, without starting a cluster. Until 2026-11-21 the token was `authlease-3354335`, checked for every `k ≤ 1000`; the theorem's `k ≤ 1000`
stays (its proof needs only the ports' bound), but its premises on the ids are checked only for `k ≤ 300`: above,
they may be false of the real ids, and the theorem then says nothing.

**The closed theorem retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorem `etcd_authlease_safe` (with `etcd_authlease_adequate`, `Adequacy.lean` and `PkgTable.lean`) is gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) subsumes it (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_authlease.wp_Main`). -/
theorem authlease_Main [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_authlease.Main.spec (GF := GF) (hG := hG) :=
  etcd_authlease.wp_Main

end results

#print axioms authlease_Main

end EtcdGrove
end Perennial
