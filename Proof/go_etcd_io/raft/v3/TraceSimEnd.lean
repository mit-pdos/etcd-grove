/-
Lean-first (no Rocq counterpart). Trace-check's layer B (2026-11-09): the run at the end, as `Main`'s
pure obligations take it (`tracecheck/MainPure.lean`, `RunAccepted`).

`simRun_runRel`: the simulation's run (`SimRun`, a `simInv` clause) is, once the whole trace's
initial state and servers are the voters' (`newTrace` reads them from the bootstrap lines: layer B's
bootstrap clause, once every voter's are logged), a run through every line of the whole trace
(`Trace.RunRel`), which gives `CheckTrace`'s no-evaluation-error premise and its verdict
(`Trace.RunRel.checkTraceOk`, `Trace.RunRel.checkTraceRel_eq`). `simRun_accepts`
(`TraceSimGhost.lean`) is its corollary for `TraceAccepts`.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris go_etcd_io.raft.v3

namespace TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The run through every line of the whole trace**, from the simulation's run, once the whole
trace's initial state and servers are the voters'. -/
theorem simRun_runRel (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (t : Etcdraft.Trace) :
    SimRun C L σ → Etcdraft.newTrace (L.map evConv) = .ok t →
    t.init = simInit C → t.server = confAbs C → t.initSrv = confAbs C →
    ∃ ts, t.RunRel t.len ts := by
  intro hrun hnt hinit hsrv hisrv
  rcases hrun with ⟨hL, -⟩ | ⟨lines, ts, hl, hr, -, -⟩
  · subst hL; exact absurd hnt (Etcdraft.newTraceWith_nil false false t)
  · obtain ⟨hpl, hb⟩ := newTraceWith_lines _ t hnt
    rw [hl] at hpl
    cases hpl
    have heq : linesTrace C t.lines = t := by
      unfold linesTrace
      rcases t with ⟨tl, ts, ti, tb, tin⟩
      simp only at hinit hsrv hisrv hb ⊢
      subst hinit hsrv hisrv hb
      rfl
    rw [heq] at hr
    have hlen : t.len = L.length := by
      simpa using Etcdraft.newTraceWith_len _ false false t hnt
    rw [← hlen] at hr
    exact ⟨ts, hr⟩

end ghost

end TraceSim

end EtcdGrove
end Perennial
