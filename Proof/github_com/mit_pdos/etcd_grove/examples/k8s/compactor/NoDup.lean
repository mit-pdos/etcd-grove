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

end k8s_compactor
end EtcdGrove
end Perennial
