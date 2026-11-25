/- Lean-first (no Rocq counterpart).

# `raft/kvraft/cmd/kvraft-udp`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): `kvraft_udp_robust`'s and
`kvraft_udp_robust_example`'s premises hold together with `Robust`'s antecedents. As kvraft's witness
(`KvRaft/Proof/.../kvraft/TopLevelWitness.lean`), with the UDP extension's initial states: every
machine starts as `udpStart` (kvraft's start, and no socket: `Udp.UdpLocal.init`), the network with no
connection and no datagram (`Net.NetGlobal.init`, `Udp.UdpGlobal.init`). Nothing is left out. Checked
by `etc/premise-witness.py`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.cmd.kvraft_udp.TopLevelRobustness
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TopLevelWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft_udp

open NetFsUdp kvraft Robustness Fs

section witness
attribute [local instance] kvraftUdpExts kvraftUdpExtsSemantics kvraftUdpExts_hasNet kvraftUdpExts_hasFs
  kvraftUdpExts_hasUdp
variable [go_gctx : GoGlobalContext]

/-- Every machine's start: a fresh process, no listener, no socket, the empty root `witnessDir`. -/
def udpStart [lctx : GoLocalContext] : state :=
  freshState ((default : Net.NetLocal), fsOneRoot witnessDir, (default : Udp.UdpLocal), ())

/-- The network's start: no connection, no datagram. -/
def udpStartG : GlobalState := ⟨((default : Net.NetGlobal), (), (default : Udp.UdpGlobal), ()), ∅⟩

theorem udpStart_fs [lctx : GoLocalContext] : fsOf udpStart = fsOneRoot witnessDir := rfl

theorem udpStart_dir [lctx : GoLocalContext] :
    witnessDir ∈ (fsOf udpStart).fs.roots.map (·.1) ∧
      ∀ c, (fsOf udpStart).lookup (joinPath witnessDir [c]) = none := by
  rw [udpStart_fs]
  exact ⟨by simp [fsOneRoot], fun c => fsOneRoot_lookup_child _ c⟩

theorem udpStart_initLocal [lctx : GoLocalContext] : extsInitLocal udpStart udpStartG := by
  exact ⟨rfl, fsInit_fsOneRoot _ witnessDir_rootForm, rfl, trivial⟩

theorem udpStart_initGlobal : extsInitGlobal udpStartG := by
  exts_init

theorem kvraft_udp_robust.premisesSat : premise_sat% kvraft_udp_robust.spec := by
  intros
  refine ⟨exampleConfig, witnessDir, [(go!"10.0.0.1:7001", udpStart)], udpStart, udpStartG, ?_, ?_⟩
  · intro a σ h
    obtain ⟨-, rfl⟩ : a = go!"10.0.0.1:7001" ∧ σ = udpStart := by simpa using h
    exact udpStart_dir
  · exact robustStart_same (σ := udpStart) (by simp) (fresh_freshState _) udpStart_initGlobal
      udpStart_initLocal

theorem kvraft_udp_robust_example.premisesSat : premise_sat% kvraft_udp_robust_example.spec := by
  intros
  refine ⟨udpStart, udpStart, udpStart, udpStart, udpStart, udpStart, udpStartG, ?_, ?_⟩
  · intro σ h
    obtain rfl : σ = udpStart := by simpa using h
    exact udpStart_dir
  · exact robustStart_same (σ := udpStart) (by simp) (fresh_freshState _) udpStart_initGlobal
      udpStart_initLocal

end witness

end kvraft_udp
end EtcdGrove
end Perennial

end
