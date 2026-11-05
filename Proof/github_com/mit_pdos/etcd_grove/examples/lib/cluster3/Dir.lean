/-
**The cluster's peer-URL directory** (`dir3`, `Defs.lean`; until 2026-11-05 `partition/Alloc.lean`'s,
at linkv3p's peer addresses; rafthttp stage 6d, 2026-10-24). Lean-first (no Rocq counterpart).
Its hosts are the three peer addresses (`dir3_host`, what the cluster's allocation `etcdstart.alloc3`
takes); it is well formed (`dir3_ok`, `NewServer`'s `netDirOk`) for a configuration meeting
`cfgOk` and ids not `0`; it names the peers (`dir3_dirsOk`, `rafthttp.bootCfg`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section dir
variable [GooseExts]

/-- A member of the directory: the first id it matches, with that id's peer address. -/
theorem dir3_mem (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (id₁ id₂ id₃ id : w64) (h : GoString) (hm : go!"http://" ++ h ∈ dir3 cfg id₁ id₂ id₃ id) :
    (id = id₁ ∧ h = cfg.Peer1') ∨ (id ≠ id₁ ∧ id = id₂ ∧ h = cfg.Peer2') ∨
      (id ≠ id₁ ∧ id ≠ id₂ ∧ id = id₃ ∧ h = cfg.Peer3') := by
  unfold dir3 at hm
  split at hm
  · left; exact ⟨by assumption, by simpa using hm⟩
  split at hm
  · right; left; exact ⟨by assumption, by assumption, by simpa using hm⟩
  split at hm
  · right; right; exact ⟨by assumption, by assumption, by assumption, by simpa using hm⟩
  · simp at hm

/-- A host of the directory is one of the three peer addresses (2026-10-24, rafthttp stage 6d). -/
theorem dir3_host (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (id₁ id₂ id₃ id : w64) (h : GoString) (hm : go!"http://" ++ h ∈ dir3 cfg id₁ id₂ id₃ id) :
    h = cfg.Peer1' ∨ h = cfg.Peer2' ∨ h = cfg.Peer3' := by
  rcases dir3_mem cfg id₁ id₂ id₃ id h hm with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **The cluster's directory is well formed** (`netDirOk`, `NewServer`'s premise; rafthttp stage
6d): no member `0`, each peer address one member's, plain `http://` URLs. -/
theorem dir3_ok (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (hcfg : cfgOk cfg) (id₁ id₂ id₃ : w64) (h1 : id₁ ≠ W64 0) (h2 : id₂ ≠ W64 0)
    (h3 : id₃ ≠ W64 0) : netDirOk (dir3 cfg id₁ id₂ id₃) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dir3
    rw [if_neg (fun e => h1 (by rw [← e]; rfl)), if_neg (fun e => h2 (by rw [← e]; rfl)),
      if_neg (fun e => h3 (by rw [← e]; rfl))]
  · intro i j h hi hj
    have p12 := hcfg.p12
    have p13 := hcfg.p13
    have p23 := hcfg.p23
    rcases dir3_mem cfg id₁ id₂ id₃ i h hi with ⟨hi1, hh⟩ | ⟨hi1, hi2, hh⟩ | ⟨hi1, hi2, hi3, hh⟩ <;>
    rcases dir3_mem cfg id₁ id₂ id₃ j h hj with ⟨hj1, hh'⟩ | ⟨hj1, hj2, hh'⟩ |
      ⟨hj1, hj2, hj3, hh'⟩ <;>
    subst hh <;> simp_all
  · intro i s hs
    unfold dir3 at hs
    split at hs
    · simp at hs; subst hs; exact hcfg.pp1
    split at hs
    · simp at hs; subst hs; exact hcfg.pp2
    split at hs
    · simp at hs; subst hs; exact hcfg.pp3
    · simp at hs

/-- **The cluster's directory names the peers** (`rafthttp.bootCfg`, `NewServer`'s premise;
2026-11-03, the final whole-`bootOk` review's M2): its members are the ids, which the peers
permute. -/
theorem dir3_dirsOk (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (id₁ id₂ id₃ : w64) (ps : List w64) (hperm : ps.Perm [id₁, id₂, id₃]) :
    rafthttp.bootCfg (dir3 cfg id₁ id₂ id₃) ps := by
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

end dir

end cluster3
end EtcdGrove
end Perennial
