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

/-- **Endpoints claimed for one cluster** (`k8s.epOf_alloc` over a list of distinct endpoints, none
claimed yet): `MainPartition`'s `k` bridges, for the API servers sharing the process's compactor. -/
theorem epOfs_alloc [sync.Assumptions] (γk : KVNames) :
    ∀ (L : List GoString) (M : GMap GoString GName), L.Nodup → (∀ a ∈ L, M.lookup a = none) →
      k8s.regAuth M ⊢ |==> ∃ M', k8s.regAuth M' ∗
        [∗list] ep ∈ L, k8s.epOf (GF := GF) ep γk (fun _ => iprop(True))
  | [], M, _, _ => by
    iintro Hreg
    imodintro
    iexists M
    iframe
    iapply BigSepL.bigSepL_nil.2; itrivial
  | a :: L, M, hnd, hfree => by
    iintro Hreg
    imod (k8s.epOf_alloc M a γk (fun _ => iprop(True)) (hfree a (by simp))) $$ Hreg
      with ⟨%γa, Hreg, #Hep⟩
    have hnd' := List.nodup_cons.1 hnd
    imod (epOfs_alloc γk L (M.insert a γa) hnd'.2 (fun b hb => by
      have hne : a ≠ b := fun h => hnd'.1 (h ▸ hb)
      show (<[a := γa]> M) !! b = none
      rw [GMap.lookup_insert_ne M γa hne]
      exact hfree b (by simp [hb]))) $$ Hreg with ⟨%M', Hreg, Heps⟩
    imodintro
    iexists M'
    iframe Hreg
    iapply BigSepL.bigSepL_cons.2
    iframe Hep
    iexact Heps

end mainVars

end k8s_compactor
end EtcdGrove
end Perennial
