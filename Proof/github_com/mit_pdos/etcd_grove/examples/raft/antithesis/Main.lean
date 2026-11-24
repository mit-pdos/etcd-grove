/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Main.lean`, over its callees' specs.

`RunCluster(DefaultConfig())` returns the run over (`runOver`: the stream accepted at `cfg3`,
bounded, with no configuration change, and `Nodes = 3`); `c.Servers()` twice gives `cfg3`'s sets,
so the `check.Config` built is `cfg3`; `c.Events()` gives the stream with its facts, which are
`check.Run`'s premises; its verdict is `Accepts`' one, of kind `Accepted`, so no panic.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DefaultConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__Servers
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__Events
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- `DefaultConfig()` meets `RunCluster`'s premise. -/
theorem cfgOk_defaultCfg [GooseExts] : CfgOk defaultCfg := by
  refine ⟨rfl, ?_, ?_⟩ <;> (unfold defaultCfg; simp only; word)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Main.wp_proof
    (wp_DefaultConfig : DefaultConfig.spec (GF := GF) (hG := hG))
    (wp_RunCluster : RunCluster.spec (GF := GF) (hG := hG))
    (wp_Servers : Cluster.Servers.spec (GF := GF) (hG := hG))
    (wp_Events : Cluster.Events.spec (GF := GF) (hG := hG))
    (wp_Run : AntCheck.Run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro _ Hrb
  wp_start as -
  ihave #Hck : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check $$ []
  · iPkgInit
  wp_apply wp_DefaultConfig
  wp_apply (wp_RunCluster Hrb defaultCfg cfgOk_defaultCfg) as %c Hrun
  try wp_auto
  iunfold runOver at Hrun
  icases Hrun with ⟨%r, %γr, %evs, #Hr, #Hrec, Hdone, #HN, %Hacc⟩
  have h3 : uint.Z (W64 3) < 2 ^ 62 := by word
  wp_apply wp_Servers c (W64 3) h3 $$ [$HN] as %u0 #Hu0
  wp_apply wp_Servers c (W64 3) h3 $$ [$HN] as %u1 #Hu1
  try wp_auto
  ipersist «$r0»
  ihave #Hcfg : AntCheck.configRO «$r0_ptr» AntSim.cfg3 $$ []
  · iunfold AntCheck.configRO
    iexists _
    iframe «$r0»
    unfold AntSim.cfg3
    iframe Hu0 Hu1
    ipureintro; rfl
  try wp_auto
  wp_apply wp_Events c $$ [Hdone] as %sl ⟨%evs', #Hsl, %Hacc'⟩
  · iunfold runOver
    iexists r, γr, evs
    iframe Hr Hrec Hdone HN
    ipureintro; exact Hacc
  obtain ⟨⟨v, Hv, Hkind⟩, Hb, Hcb⟩ := Hacc'
  have hcb : AntCheck.Config.Bounded AntSim.cfg3 := by
    unfold AntCheck.Config.Bounded; decide +kernel
  wp_apply wp_Run «$r0_ptr» AntSim.cfg3 sl evs' v $$ [] as %r' Hr'
  · iframe Hcfg Hsl
    ipureintro; exact ⟨hcb, Hb, Hcb, Hv⟩
  iunfold AntCheck.verdictRO at Hr'
  icases Hr' with ⟨%Hr'k, -⟩
  rw [Hkind] at Hr'k
  obtain ⟨Hk, -, -⟩ := Hr'k
  have hk0 : r'.Kind' = W64 0 := Hk
  simp only [hk0, decide_true, Bool.not_true]
  wp_auto
  iapply HΦ
  itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
