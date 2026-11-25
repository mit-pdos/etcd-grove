/- Lean-first (no Rocq counterpart).

# `raft/kvraft/cmd/kvraft-udp`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the premises of `kvraft_udp_robust` and
`kvraft_udp_robust_example` hold together with `Robust`'s antecedents, as for kvraft
(`raft/kvraft/TopLevelWitness.lean`): every machine is fresh, with no listener, no UDP socket, and a
file system whose only root is `/var/lib/kvraft`, an empty directory (`Robustness/FsStart.lean`); the
network has no connection and no datagram. For `kvraft_udp_robust`: one replica at `10.0.0.1:7001`,
the example's options with one bootstrap voter. Checked by `etc/premise-witness.py`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.cmd.kvraft_udp.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace kvraft_udp

open NetFsUdp kvraft
attribute [local instance] kvraftUdpExts kvraftUdpExtsSemantics kvraftUdpExts_hasNet kvraftUdpExts_hasFs

open Robustness Fs

/-- The replicas' directory, a root's form. -/
theorem kvraftUdpDir_rootForm : RootForm go!"/var/lib/kvraft" :=
  ⟨[go!"var", go!"lib", go!"kvraft"], by simp, by decide, by decide⟩

theorem kvraft_udp_robust.premisesSat : premise_sat% kvraft_udp_robust.spec := by
  intros
  refine ⟨{ exampleConfig with voters := 1 }, go!"/var/lib/kvraft",
    [(go!"10.0.0.1:7001", freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft",
      ((default : Udp.UdpLocal), ()))))],
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ((default : Udp.UdpLocal), ()))),
    (⟨((default : Net.NetGlobal), ((), ((default : Udp.UdpGlobal), ()))), ∅⟩ : GlobalState),
    ?_, robustStart_same (σ := freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft",
      ((default : Udp.UdpLocal), ())))) ?_ (fresh_freshState _) ?_ ?_⟩
  · intro a σ h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fsOneRoot_root_mem _, fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩
  · intro m hm
    simp at hm
    rcases hm with h | h <;> subst h <;> rfl
  · exact ⟨rfl, trivial, rfl, trivial⟩
  · exact ⟨rfl, fsInit_fsOneRoot _ kvraftUdpDir_rootForm, rfl, trivial⟩

theorem kvraft_udp_robust_example.premisesSat : premise_sat% kvraft_udp_robust_example.spec := by
  intros
  refine ⟨freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ((default : Udp.UdpLocal), ()))),
    (⟨((default : Net.NetGlobal), ((), ((default : Udp.UdpGlobal), ()))), ∅⟩ : GlobalState),
    ?_, robustStart_same (σ := freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft",
      ((default : Udp.UdpLocal), ())))) ?_ (fresh_freshState _) ?_ ?_⟩
  · intro σ hσ
    have h : σ = freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft",
        ((default : Udp.UdpLocal), ()))) := by
      simpa using hσ
    subst h
    exact ⟨fsOneRoot_root_mem _, fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩
  · intro m hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (h | h | h | h | h) | h <;> subst h <;> rfl
  · exact ⟨rfl, trivial, rfl, trivial⟩
  · exact ⟨rfl, fsInit_fsOneRoot _ kvraftUdpDir_rootForm, rfl, trivial⟩

end kvraft_udp
end EtcdGrove
end Perennial

end
