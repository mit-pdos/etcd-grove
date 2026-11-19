/-
**The compactor example's store writes no key twice in a revision** (Q1 (b), 2026-11-04): the
member's fact for watches (`mvcc.noDupKeys`, the arm of the create token's `watchNoDup` for a
compacting store), as `compactwatch`'s `noDupKeys_of_rounds`: the invariant's read update
(`oneChangeAu`: each revision has at most one change, `OneChange`) fires at every watched log
(`srvKVCoreM_fire`, from the member's KV facts), at a committed log it is a prefix of
(`oneChangePerKey_of_one`). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Aus
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OnceUpTo
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
theorem srvOnce_of_one [go_etcd_io.raft.v3.Assumptions] [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (V : client.WEnv GF) (γ : KVNames) (hst : γ.st = V.kst) :
    client.srvKVFacts V ∗ kvReadAu γ (fun σ => iprop(⌜OneChange σ⌝)) ⊢ v3rpc.srvOnce V.W :=
  etcdstart.srvOnce_of_plan V γ hst (fun ch => ∀ cs ∈ ch, cs.length ≤ 1) (fun _ h cs hcs => by
    have := h cs hcs
    match cs, this with
    | [], _ => simp
    | [_], _ => simp)

end proof

section mainVars
-- `Main.lean`'s section variables, which `loop_step`'s statement takes (moved from there unchanged)
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

/-- The API servers' loop's counters: one more round, one more `Add`. -/
theorem loop_step (n : w64) (k : w32)
    (hk : sint.Z k ≤ sint.Z n ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ 5 ∧ 0 ≤ sint.Z k)
    (h3 : sint.Z n < sint.Z (W64 5)) :
    sint.Z (k + W32 1) ≤ sint.Z (n + W64 1) ∧ 0 ≤ sint.Z (n + W64 1) ∧ sint.Z (n + W64 1) ≤ 5 ∧
      0 ≤ sint.Z (k + W32 1) := by
  obtain ⟨h1, h2, h4, h5⟩ := hk
  word

end mainVars

end k8s_compactor
end EtcdGrove
end Perennial
