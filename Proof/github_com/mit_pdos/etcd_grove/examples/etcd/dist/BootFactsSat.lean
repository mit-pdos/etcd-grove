/- Lean-first (no Rocq counterpart).

# `etcd/dist`: `BootFacts` holds at Go's values of a well-formed deployment

`etcd_robust_nocrash.spec`'s premise `BootFacts d boot` (`TopLevelDefs.lean`: `BootCore (distPs d) (distCtxs d)
boot`, at the peers and contexts Go computes from the deployment) is satisfiable together with the deployment's
check: `BootFacts.sat`, at the one-member deployment `satD` of `putget_safe`'s witness (the member `putgetd` at
the peer address `10.77.1.1:2380`, the client address `10.77.1.1:2379`, the token `putgetd`, no workload), whose
peers and contexts are that witness's (`pgId`, `pgCtx`: the kernel's SHA-1, `pgId_eq`) and whose bootstrap log is
its `pgBoot` (`pgBootCore`). The statements' whole witness (`premise_sat%`) is still missing
(`etc/premise-witness-baseline.txt`); this is its `BootFacts` part.

A defs module.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.BootGoD
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelWitness

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_putget_dist

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- **The deployment**: `putget_safe`'s member, its token its name, the compactor off, snapshots every entry, no
token provider, no workload. -/
def satD : Deployment where
  members := [⟨etcd_putget_dist.name, peerA, clientA⟩]
  token := etcd_putget_dist.name
  cfg := ⟨go!"", W64 0, W64 1, W64 1, false⟩
  workloads := []
  nodes := []

theorem satD_ids : satD.ids = [pgId] := by
  simp only [Deployment.ids, satD, List.map_cons, List.map_nil]
  rw [← BootGoD.memberID_one, pgId_eq]

/-- **The deployment passes Go's check.** -/
theorem satD_wf : satD.WellFormed := by
  refine ⟨⟨satD.members, satD.token, ⟨.off, 1, 1, false⟩, [], []⟩, ⟨rfl, rfl, ?_, List.Forall₂.nil, rfl⟩, ?_⟩
  · unfold typed.ServerCfg.Encodes satD; decide
  · have e : typed.Deployment.ids ⟨satD.members, satD.token, ⟨.off, 1, 1, false⟩, [], []⟩ = [pgId] := satD_ids
    have ha : typed.Deployment.addrs ⟨satD.members, satD.token, ⟨.off, 1, 1, false⟩, [], []⟩ =
        [peerA, clientA] := rfl
    unfold typed.Deployment.WellFormed leaseIdsApart typed.maxMembers typed.maxLen typed.maxNameLen
    rw [e, ha]
    refine ⟨by simp [satD], by simp [satD], ?_, ?_, ?_, rfl, by simp, by simp, ?_, ?_, by simp, ?_, ?_, ?_,
      by simp, by simp, by simp, by simp, by simp [satD], ?_, ?_, ?_⟩
    · intro m hm
      simp only [satD, List.mem_singleton] at hm
      subst hm
      decide +kernel
    · intro a h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> decide +kernel
    · decide +kernel
    · simp only [List.mem_singleton, forall_eq]
      unfold pgId; decide +kernel
    · simp only [List.mem_singleton, forall_eq]
      unfold pgId; decide +kernel
    · show satD.token ≠ []
      decide +kernel
    · show typed.ServerCfg.Supported ⟨.off, 1, 1, false⟩
      decide
    · show typed.Compatible []
      decide
    · intro m hm
      simp only [satD, List.mem_singleton] at hm
      subst hm
      decide +kernel
    · intro a h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> decide +kernel
    · show satD.token.length ≤ 255
      decide +kernel

theorem satD_ps : distPs satD = [pgId] :=
  List.perm_singleton.1 ((BootGoD.distPs_perm satD_wf).trans (by rw [satD_ids]))

theorem satD_members : bootGo.members (distURLs satD) satD.token = [pgMember] := by
  have hps := satD_ps
  unfold distPs bootGo.ps at hps
  obtain ⟨x, hx, -⟩ := List.map_eq_singleton_iff.1 hps
  have hmem : x ∈ bootGo.members (distURLs satD) satD.token := by rw [hx]; exact List.mem_singleton_self _
  rw [hx]
  obtain ⟨mm, hmm, rfl⟩ := (BootGoD.mem_members satD_wf (BootGoD.distURLs_initOf satD) x).1 hmem
  simp only [satD, List.mem_singleton] at hmm
  subst hmm
  simp only [BootGoD.memberD, pgMember, satD, List.cons.injEq, and_true]
  rw [← BootGoD.memberID_one, pgId_eq]

theorem satD_ctxs : distCtxs satD = [pgCtx] := by
  unfold distCtxs bootGo.ctxs
  rw [satD_members]
  rfl

/-- **`BootFacts` is satisfiable at Go's values, with the deployment's check.** -/
theorem BootFacts.sat : ∃ (d : Deployment) (boot : List LogEntry), d.WellFormed ∧ BootFacts d boot := by
  refine ⟨satD, pgBoot, satD_wf, ?_⟩
  show BootCore (distPs satD) (distCtxs satD) pgBoot
  rw [satD_ps, satD_ctxs]
  exact pgBootCore

end etcd_dist
end EtcdGrove
end Perennial

end
