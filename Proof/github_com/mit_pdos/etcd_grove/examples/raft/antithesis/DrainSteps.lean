/-
Lean-first (no Rocq counterpart). #33 S4: **the pure steps of `Cluster.drain`'s reports**, each the
`hstep` premise of `report_au` (`DrainReports.lean`): the report's `antSim_*` lemma at the
invariant's state (the view the caller's, the sent list past the caller's lower bound, raft's facts
grown to the report's `Q`), then the run after it (`antRun_snoc`) and the new view's log certified.
`antSim_ready` is taken as its statement (`Sim/Ready.lean` is still being finished).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainReports
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Send
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Apply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The `ready` report's step.** -/
theorem readyStep (GF : BundledGFunctors) [ReceiptGS GF] (hready : AntSim.antSim_ready.stmt)
    (j : Fin 3) (v : AntSim.NodeView) (ps₁ : PState) (rd : AntSim.ReadyD) (net₀ : List Msg)
    (hreach : AntSim.Reach (AntSim.nodeId j) net₀ v ps₁)
    (hout : AntSim.ReadyOutP (AntSim.nodeId j) v ps₁ rd) (hrep : AntSim.Reported v rd)
    (htold : v.byE = go!"recv" → v.told = true) (hterm : uint.Z v.ps.term + 1 < 2 ^ 64)
    (hnums : (AntSim.evReady (AntSim.nodeId j) v.byE rd.role rd.term rd.vote rd.commit
      rd.ents).NumsOk)
    (hrf : antRunFits GF) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin 3 → AntSim.NodeView)
      (net : List Msg) (G : AntSim.RaftFacts),
      AntRun evs S V net → AntSim.RaftLaws G → AntSim.GlobalOk S net G →
      (∀ i : Fin 3, (V i).ps.log ∈ G.logs) → V j = v →
      AntSim.ReadyFacts G (AntSim.nodeId j) ps₁ → net₀ <+: net →
      Stream.Fits GF (evs ++ [AntSim.evReady (AntSim.nodeId j) v.byE rd.role rd.term rd.vote
        rd.commit rd.ents]) →
      ∃ S', AntRun (evs ++ [AntSim.evReady (AntSim.nodeId j) v.byE rd.role rd.term rd.vote
          rd.commit rd.ents]) S' (AntSim.setV V j (v.afterReady ps₁ rd)) (net ++ []) ∧
        AntSim.GlobalOk S' (net ++ []) G ∧ (v.afterReady ps₁ rd).ps.log ∈ G.logs := by
  intro evs S V net G hR hL hG _ hVj hQ hpre hfit
  subst hVj
  obtain ⟨S', hP', hA', hG'⟩ := hready S V net evs G j ps₁ rd hR.1 hR.2.1 hL hG
    (hreach.mono hpre) hout hrep htold hQ hterm
  refine ⟨S', ?_, ?_, hQ.1⟩
  · rw [List.append_nil]
    exact antRun_snoc GF hR hP' hA' hnums (chgOk_evReady _ _ _ _ _ _ _) hfit hrf
  · rw [List.append_nil]; exact hG'

/-- **A `send` report's step** (the next pending message `q`). -/
theorem sendStep (GF : BundledGFunctors) [ReceiptGS GF] (j : Fin 3) (v : AntSim.NodeView)
    (q : Msg) (rest : List Msg) (net₀ : List Msg) (hpend : v.pend = q :: rest)
    (htold : v.byE = go!"recv" → v.told = true)
    (hnums : (AntSim.evSend (AntSim.nodeId j) v.byE q).NumsOk) (hrf : antRunFits GF) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin 3 → AntSim.NodeView)
      (net : List Msg) (G : AntSim.RaftFacts),
      AntRun evs S V net → AntSim.RaftLaws G → AntSim.GlobalOk S net G →
      (∀ i : Fin 3, (V i).ps.log ∈ G.logs) → V j = v → AntSim.MsgFacts G q → net₀ <+: net →
      Stream.Fits GF (evs ++ [AntSim.evSend (AntSim.nodeId j) v.byE q]) →
      ∃ S', AntRun (evs ++ [AntSim.evSend (AntSim.nodeId j) v.byE q]) S'
          (AntSim.setV V j { v with pend := rest }) (net ++ [q]) ∧
        AntSim.GlobalOk S' (net ++ [q]) G ∧ ({ v with pend := rest } : AntSim.NodeView).ps.log ∈ G.logs := by
  intro evs S V net G hR hL hG hlogs hVj hQ _ hfit
  subst hVj
  obtain ⟨S', hP', hA', hG'⟩ := AntSim.antSim_send S V net evs G j q rest hR.1 hR.2.1 hL hG hpend
    htold hQ
  exact ⟨S', antRun_snoc GF hR hP' hA' hnums (chgOk_evSend _ _ _) hfit hrf, hG', hlogs j⟩

/-- **The `apply` report's step.** -/
theorem applyStep (GF : BundledGFunctors) [ReceiptGS GF] (j : Fin 3) (v : AntSim.NodeView)
    (net₀ : List Msg) (hce : v.ce ≠ []) (htold : v.byE = go!"recv" → v.told = true)
    (hnums : (AntSim.evApply (AntSim.nodeId j) v.byE v.ce).NumsOk) (hrf : antRunFits GF) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin 3 → AntSim.NodeView)
      (net : List Msg) (G : AntSim.RaftFacts),
      AntRun evs S V net → AntSim.RaftLaws G → AntSim.GlobalOk S net G →
      (∀ i : Fin 3, (V i).ps.log ∈ G.logs) → V j = v → True → net₀ <+: net →
      Stream.Fits GF (evs ++ [AntSim.evApply (AntSim.nodeId j) v.byE v.ce]) →
      ∃ S', AntRun (evs ++ [AntSim.evApply (AntSim.nodeId j) v.byE v.ce]) S'
          (AntSim.setV V j { v with delivered := v.delivered ++ v.ce, ce := [] }) (net ++ []) ∧
        AntSim.GlobalOk S' (net ++ []) G ∧
        ({ v with delivered := v.delivered ++ v.ce, ce := [] } : AntSim.NodeView).ps.log ∈ G.logs := by
  intro evs S V net G hR hL hG hlogs hVj _ _ hfit
  subst hVj
  obtain ⟨S', hP', hA', hG'⟩ := AntSim.antSim_apply S V net evs G j hR.1 hR.2.1 hL hG hce htold
  refine ⟨S', ?_, ?_, hlogs j⟩
  · rw [List.append_nil]
    exact antRun_snoc GF hR hP' hA' hnums (chgOk_evApply _ _ _) hfit hrf
  · rw [List.append_nil]; exact hG'

end pure

end AntHarness
end EtcdGrove
end Perennial
