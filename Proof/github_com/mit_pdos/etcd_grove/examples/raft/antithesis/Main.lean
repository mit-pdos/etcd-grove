/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Main.lean`, over its callees' specs.

`MainScope()` is `mainScope = b1Scope`; `DrawMode` draws a mode within it (`InScope`), and
`RunCluster(DefaultConfig(), mode)` returns the run over (`runOver`). `c.CheckConfig()` builds the
binding's constants of the mode (`Nodes`, `Voters`, `Boot`), which are `R.cfg` for the run's `R`
(`ModeRun`; the mode the one `c.Events()` names, the same read-only field); `c.Events()` gives the
stream with its facts, which are `check.Run`'s premises (`R.cfg`'s sets at most nine names); its
verdict is `Accepts`' one, of kind `Accepted`, so no panic.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DefaultConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrawMode
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.MainScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__CheckConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__Events
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Run
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- `DefaultConfig()` meets `RunCluster`'s premise (a positive tick). -/
theorem cfgOk_defaultCfg [GooseExts] : CfgOk defaultCfg := by
  unfold CfgOk defaultCfg; simp only; word

/-- A mode within a scope has at most nine servers, and no more voters than servers
(`CheckConfig`'s premise). -/
theorem inScope_sizes [GooseExts] {s : H.Scope} {m : H.Mode} (h : InScope s m) :
    uint.Z m.Voters' ≤ uint.Z m.Nodes' ∧ uint.Z m.Nodes' ≤ 9 := by
  obtain ⟨hN, hV, -⟩ := h
  rcases hV with hV | ⟨-, hN5, hV3⟩
  · rw [hV]; rcases hN with hN | hN <;> rw [hN] <;> decide
  · rw [hN5, hV3]; decide

/-- The run's binding constants are bounded (`check.Run`'s premise): at most nine names. -/
theorem runCfg_bounded (R : AntSim.RunCfg) : AntCheck.Config.Bounded R.cfg := by
  have hN := R.hK
  have h1 := AntCheck.setOf_length_le (AntSim.namesL R.N)
  have h2 := AntCheck.setOf_length_le (AntSim.namesL R.K)
  have l1 : (AntSim.namesL R.N).length = R.N := by simp [AntSim.namesL]
  have l2 : (AntSim.namesL R.K).length = R.K := by simp [AntSim.namesL]
  unfold AntCheck.Config.Bounded AntSim.RunCfg.cfg AntCheck.numBound
  simp only
  constructor <;> omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Main.wp_proof
    (wp_DefaultConfig : DefaultConfig.spec (GF := GF) (hG := hG))
    (wp_MainScope : MainScope.spec (GF := GF) (hG := hG))
    (wp_DrawMode : DrawMode.spec (GF := GF) (hG := hG))
    (wp_RunCluster : RunCluster.spec (GF := GF) (hG := hG))
    (wp_CheckConfig : Cluster.CheckConfig.spec (GF := GF) (hG := hG))
    (wp_Events : Cluster.Events.spec (GF := GF) (hG := hG))
    (wp_Run : AntCheck.Run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro _ Hrb
  wp_start as Htok
  ihave #Hck : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check $$ []
  · iPkgInit
  wp_apply wp_DefaultConfig
  wp_apply wp_MainScope
  wp_apply wp_DrawMode as %mode %Hsc
  rw [show mainScope = b1Scope from rfl] at Hsc
  wp_apply (wp_RunCluster Hrb defaultCfg mode cfgOk_defaultCfg Hsc) $$ [$Htok] as %c ⟨Hrun, -⟩
  try wp_auto
  ihave Hrun' := Hrun
  iunfold runOver at Hrun'
  icases Hrun' with ⟨%r, %γr, %evs, %m, %R, #Hr, #Hrec, Hdone, #Hm, %Hacc⟩
  wp_apply wp_CheckConfig c m $$ [$Hm] as %p #Hp
  · ipureintro; exact inScope_sizes Hacc.1
  wp_apply wp_Events c b1Scope $$ [Hr Hrec Hdone Hm] as %sl ⟨%evs', %m', %R', #Hsl, #Hm', %Hacc'⟩
  · iunfold runOver
    iexists r, γr, evs, m, R
    iframe Hr Hrec Hdone Hm
    ipureintro; exact Hacc
  ihave %Hmm := typedPointsto_agree_wand _ _ _ _ _ $$ Hm Hm'
  subst Hmm
  obtain ⟨-, hMR, ⟨v, Hv, Hkind⟩, Hb, Hcb⟩ := Hacc'
  obtain ⟨hN, hK, hB, -⟩ := hMR
  ihave #Hp' : AntCheck.configRO p R'.cfg $$ [Hp]
  · unfold AntSim.RunCfg.cfg; rw [hN, hK, hB]; iexact Hp
  wp_apply wp_Run p R'.cfg sl evs' v $$ [] as %r' Hr'
  · iframe Hp' Hsl
    ipureintro; exact ⟨runCfg_bounded R', Hb, Hcb, Hv⟩
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
