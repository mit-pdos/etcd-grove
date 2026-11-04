/-
**The instance's invariant at every member's KV names** (the partition plan's S3a, 2026-10-20).
Lean-first (no Rocq counterpart). The cluster's ghost state is the examples' shared `etcdstart.alloc3`
(since 2026-10-22, D33; until then this file's `cluster3_alloc`), whose members' KV names agree in
state variable; `linkvInv_congr` makes the instance's invariant, allocated at the
first member's names (`linkvInv_alloc_boot`), the other members' too (D21 M4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A host of the directory is one of the three peer addresses (2026-10-24, rafthttp stage 6d). -/
theorem dir3_host (id₁ id₂ id₃ id : w64) (h : GoString)
    (hm : go!"http://" ++ h ∈ dir3 id₁ id₂ id₃ id) : h = peerAddr₁ ∨ h = peerAddr₂ ∨ h = peerAddr₃ := by
  unfold dir3 at hm
  split at hm
  · left; simpa using hm
  split at hm
  · right; left; simpa using hm
  split at hm
  · right; right; simpa using hm
  · simp at hm

/-- **`Main`'s directory is well formed** (`netDirOk`, `NewServer`'s premise; rafthttp stage 6d):
no member `0`, each peer address one member's, plain `http://` URLs. -/
theorem dir3_ok (id₁ id₂ id₃ : w64) (h1 : id₁ ≠ W64 0) (h2 : id₂ ≠ W64 0) (h3 : id₃ ≠ W64 0) :
    netDirOk (dir3 id₁ id₂ id₃) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dir3
    rw [if_neg (fun e => h1 (by rw [← e]; rfl)), if_neg (fun e => h2 (by rw [← e]; rfl)),
      if_neg (fun e => h3 (by rw [← e]; rfl))]
  · intro i j h hi hj
    unfold dir3 at hi hj
    split at hi <;> split at hj <;> (try split at hi) <;> (try split at hj) <;>
      (try split at hi) <;> (try split at hj) <;> simp_all <;> (try decide)
  · intro i s hs
    unfold dir3 at hs
    split at hs
    · simp at hs; subst hs; decide
    split at hs
    · simp at hs; subst hs; decide
    split at hs
    · simp at hs; subst hs; decide
    · simp at hs

/-- **`Main`'s directory names the peers** (`rafthttp.bootCfg`, `NewServer`'s premise; 2026-11-03, the final
whole-`bootOk` review's M2): its members are the ids, which the peers permute. -/
theorem dir3_dirsOk (id₁ id₂ id₃ : w64) (ps : List w64) (hperm : ps.Perm [id₁, id₂, id₃]) :
    rafthttp.bootCfg (dir3 id₁ id₂ id₃) ps := by
  refine rafthttp.bootCfg_of _ ps (fun f => ?_) (by rw [hperm.length_eq]; simp)
  rw [hperm.mem_iff]
  unfold dir3
  constructor
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_cases h1 : f = id₁
    · exact Or.inl h1
    by_cases h2 : f = id₂
    · exact Or.inr (Or.inl h2)
    by_cases h3 : f = id₃
    · exact Or.inr (Or.inr h3)
    rw [if_neg h1, if_neg h2, if_neg h3] at h
    exact absurd rfl h
  · intro hm
    split
    · simp
    split
    · simp
    split
    · simp
    · simp_all

/-- **The instance's invariant at another member's KV names**: `linkvInv γ γk` reads `γk`'s state
variable (through `etcdKV`) only, which a cluster's members share (D21 M4;
`etcdstart.alloc3`'s equalities), so the invariant allocated at one member's names
(`linkvInv_alloc_boot`) is every member's. -/
theorem linkvInv_congr (γ : etcd_txnlin.LinkvNames) (γk γk' : KVNames) (hst : γk.st = γk'.st) :
    etcd_txnlin.linkvInv (GF := GF) γ γk = etcd_txnlin.linkvInv γ γk' := by
  unfold etcd_txnlin.linkvInv etcd_txnlin.linkvInvBody
  simp only [etcdKV_congr γk γk' hst]

end alloc

end etcd_partition
end EtcdGrove
end Perennial
