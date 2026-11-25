/- Lean-first (no Rocq counterpart).

# `raft/kvnet/cmd/kvudp`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the premises of `raft_kvudp_robust` and
`raft_kvudp_robust_example` hold together with `Robust`'s antecedents, as for kvnet
(`raft/kvnet/TopLevelWitness.lean`): every machine is fresh, with no listener, no UDP socket, and a
file system whose only root is `/var/lib/kvnet`, an empty directory (`Robustness/FsStart.lean`); the
network has no connection and no datagram. For `raft_kvudp_robust`: one replica at `10.0.0.1:7001`,
the example's options with one bootstrap voter. Checked by `etc/premise-witness.py`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.cmd.kvudp.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace raft_kvudp

open NetFsUdp raft_kvnet
attribute [local instance] kvudpExts kvudpExtsSemantics kvudpExts_hasNet kvudpExts_hasFs

open Robustness Fs

/-- The replicas' directory, a root's form. -/
theorem kvudpDir_rootForm : RootForm go!"/var/lib/kvnet" :=
  ⟨[go!"var", go!"lib", go!"kvnet"], by simp, by decide, by decide⟩

theorem raft_kvudp_robust.premisesSat : premise_sat% raft_kvudp_robust.spec := by
  intros
  refine ⟨{ exampleConfig with voters := 1 }, go!"/var/lib/kvnet",
    [(go!"10.0.0.1:7001", freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet",
      ((default : Udp.UdpLocal), ()))))],
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ((default : Udp.UdpLocal), ()))),
    (⟨((default : Net.NetGlobal), ((), ((default : Udp.UdpGlobal), ()))), ∅⟩ : GlobalState),
    ?_, robustStart_same (σ := freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet",
      ((default : Udp.UdpLocal), ())))) ?_ (fresh_freshState _) ?_ ?_⟩
  · intro a σ h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fsOneRoot_root_mem _, fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩
  · intro m hm
    simp at hm
    rcases hm with h | h <;> subst h <;> rfl
  · exact ⟨rfl, trivial, rfl, trivial⟩
  · exact ⟨rfl, fsInit_fsOneRoot _ kvudpDir_rootForm, rfl, trivial⟩

theorem raft_kvudp_robust_example.premisesSat : premise_sat% raft_kvudp_robust_example.spec := by
  intros
  refine ⟨freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ((default : Udp.UdpLocal), ()))),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ((default : Udp.UdpLocal), ()))),
    (⟨((default : Net.NetGlobal), ((), ((default : Udp.UdpGlobal), ()))), ∅⟩ : GlobalState),
    ?_, robustStart_same (σ := freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet",
      ((default : Udp.UdpLocal), ())))) ?_ (fresh_freshState _) ?_ ?_⟩
  · intro σ hσ
    have h : σ = freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet",
        ((default : Udp.UdpLocal), ()))) := by
      simpa using hσ
    subst h
    exact ⟨fsOneRoot_root_mem _, fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩
  · intro m hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (h | h | h | h | h) | h <;> subst h <;> rfl
  · exact ⟨rfl, trivial, rfl, trivial⟩
  · exact ⟨rfl, fsInit_fsOneRoot _ kvudpDir_rootForm, rfl, trivial⟩

end raft_kvudp
end EtcdGrove
end Perennial

end
