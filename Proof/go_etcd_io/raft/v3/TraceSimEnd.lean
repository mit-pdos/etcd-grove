/-
Lean-first (no Rocq counterpart). Trace-check's layer B (2026-11-09): the run at the end, as `Main`'s
pure obligations take it (`tracecheck/MainPure.lean`, `RunAccepted`).

`simRun_runRel`: the simulation's run (`SimRun`, a `simInv` clause) is, once the whole trace's
initial state and servers are the voters' (`newTrace` reads them from the bootstrap lines: layer B's
bootstrap clause, once every voter's are logged), a run through every line of the whole trace
(`Trace.RunRel`), which gives `CheckTrace`'s no-evaluation-error premise and its verdict
(`Trace.RunRel.checkTraceOk`, `Trace.RunRel.checkTraceRel_eq`). `simRun_accepts`
(`TraceSimGhost.lean`) is its corollary for `TraceAccepts`.

Layer B's exports (2026-11-09): `simInv_end`, what `simInv`'s body gives at the end of a run with the
recorder's half of the trace (the run `SimRun` of the recorder's `L`, and (Q13) `SimEvents L`: the
events ASCII, in scope (`ScopeOk`), the bootstrap lines' logs (`BootLogsOk`), their numbers below
`2^61`, their configuration lists within three), and `simRun_runAccepted`, `mainPure`'s
`RunAccepted L` from it and the bootstrap facts. `tracecheck/MainSim.lean` combines them with
`mainPure`. Not here: the event count (`L.length < numBound`), bounded by the run's steps
(the recorder's, outside the simulation), and the bootstrap facts (layer B's bootstrap clause).
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

/-- **`Main`'s run premise** (`tracecheck/MainPure.lean`'s `RunAccepted L`, unfolded), from the
simulation's run at the end, once the whole trace parses (`newTrace` succeeds) and its initial state
and servers are the voters' (layer B's bootstrap clause, owed: the bootstrap facts). -/
theorem simRun_runAccepted (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (t : Etcdraft.Trace)
    (hrun : SimRun C L σ) (hnt : Etcdraft.newTrace (L.map evConv) = .ok t)
    (hinit : t.init = simInit C) (hsrv : t.server = confAbs C) (hisrv : t.initSrv = confAbs C) :
    ∃ t ts, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.RunRel t.len ts := by
  obtain ⟨ts, hr⟩ := simRun_runRel C L σ t hrun hnt hinit hsrv hisrv
  exact ⟨t, ts, hnt, hr⟩

open Iris.BI Iris.ProofMode in
/-- The two halves of the trace agree, kept. -/
theorem trace_agree_keep (γt : GName) (L1 L2 : List TraceEv) :
    (traceAuth γt L1 ∗ traceFrag γt L2 : IProp GF) ⊢ (traceAuth γt L1 ∗ traceFrag γt L2) ∗ ⌜L1 = L2⌝ := by
  refine (and_intro .rfl ?_).trans persistent_and_sep.1
  iintro ⟨H1, H2⟩
  iapply trace_agree γt L1 L2 $$ H1 H2

open Iris.BI Iris.ProofMode in
/-- **The simulation's invariant at the end of a run** (its body, as `Main` holds it once the run is
over, with the recorder's half of the trace): the trace the simulation ran is the recorder's `L`,
it runs from `simInit C` (`SimRun`, for `simRun_runAccepted`), and its events have `Main`'s facts
(`SimEvents`: `ConvertEvents`' premise and `mainPure`'s hypotheses on them). -/
theorem simInv_end (C : List w64) (tn : TraceNames) (Fx : Etcdraft.State → IProp GF) (L : List TraceEv) :
    traceAuth tn.tr L ∗ simInv C tn Fx ⊢
      traceAuth tn.tr L ∗ simInv C tn Fx ∗
        ⌜∃ σ, SimRun C L σ ∧ σ.server = confAbs C ∧ SimEvents L⌝ := by
  iintro ⟨Ha, Hi⟩
  iunfold simInv at Hi
  icases Hi with ⟨%L', %σ, %A, %B, %phP, %phM, %Bt, HL, HA, HB, HBt, Hfx, %Hp⟩
  icases trace_agree_keep tn.tr L L' $$ [Ha HL] with ⟨⟨Ha, HL⟩, %hLL⟩
  · iframe
  subst hLL
  isplitl [Ha]; · iexact Ha
  isplitl [HL HA HB HBt Hfx]
  · iunfold simInv
    iexists L, σ, A, B, phP, phM, Bt
    iframe HL HA HB HBt Hfx
    ipureintro; exact Hp
  ipureintro
  obtain ⟨hrun, hsrv, -, -, -, -, -, -, -, -, hasc⟩ := Hp
  exact ⟨σ, hrun, hsrv, hasc⟩

end ghost

end TraceSim

end EtcdGrove
end Perennial
