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
`traceNumBound`, their configuration lists within the voters' number), and `simRun_runAccepted`, `mainPure`'s
`RunAccepted L` from it and the bootstrap facts. `tracecheck/MainSim.lean` combines them with
`mainPure`. Not here: the event count (`L.length < numBound`), bounded by the run's steps
(the recorder's, outside the simulation). (Amendments A7, A8) `newTrace_simInit`: what `NewTrace` computes
of complete bootstrap segments, `simInit C` (A8 gives `simInit` `bootJunk` outside the voters: the plan's
Q36 (a)). (Amendment A8, Q37) `simInv_end_bootDone`: with every voter's
`bootDone` witness, the run's end gives `NewTrace`'s success at the voters' initial state and servers.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimGhost
import Proof.go_etcd_io.raft.v3.TraceSimBootFacts

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
        ⌜∃ σ, SimRun C L σ ∧ σ.server = confAbs C ∧ SimEvents C.length L⌝ := by
  iintro ⟨Ha, Hi⟩
  iunfold simInv at Hi
  icases Hi with ⟨%L', %σ, %A, %B, %phP, %phM, %Bt, %Dn, HL, HA, HB, HBt, HDn, Hfx, %Hp⟩
  icases trace_agree_keep tn.tr L L' $$ [Ha HL] with ⟨⟨Ha, HL⟩, %hLL⟩
  · iframe
  subst hLL
  isplitl [Ha]; · iexact Ha
  isplitl [HL HA HB HBt HDn Hfx]
  · iunfold simInv
    iexists L, σ, A, B, phP, phM, Bt, Dn
    iframe HL HA HB HBt HDn Hfx
    ipureintro; exact Hp
  ipureintro
  obtain ⟨hrun, hsrv, -, -, -, -, -, -, -, -, hasc, -, -⟩ := Hp
  exact ⟨σ, hrun, hsrv, hasc⟩

end ghost

/-! ## What `NewTrace` reads of complete bootstrap segments (amendment A7, Q29) -/

section boot
variable [GooseExts]

/-- **`newTrace` of a trace whose voters' bootstrap segments are raft's and complete** (amendment A7,
Q29): it succeeds, its servers and initial servers are the voters', and its initial state is `simInit C`
(amendment A8, Q36 (a): `newTraceWith` builds an id outside the servers from the trace's first line, an
`InitState`, which is `bootJunk`, `simInit`'s server there). -/
theorem newTrace_simInit (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hC0 : C ≠ [])
    (hCl : C.length < 2 ^ 40) (hrun : SimRun C L σ) (hev : SimEvents C.length L) (hseg : BootSegs C L)
    (hdone : ∀ i ∈ C, BootDone C L i) :
    ∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.server = confAbs C ∧ t.initSrv = confAbs C ∧
      t.init = simInit C := by
  obtain ⟨t, hnt, hs, hi, hinit⟩ := newTrace_of_bootDone C L σ hC0 hCl hrun hev hseg hdone
  refine ⟨t, hnt, hs, hi, ?_⟩
  have hs' : (fun i => if i ∈ confAbs C then (simInit C).s i else bootJunk) = (simInit C).s := by
    funext i
    by_cases hi : i ∈ confAbs C
    · simp only [hi, ↓reduceIte]
    · simp only [hi, ↓reduceIte]
      exact (simInit_s_nonvoter C i hi).symm
  rw [hinit]
  show { simInit C with s := fun i => if i ∈ confAbs C then (simInit C).s i else bootJunk } = simInit C
  rw [hs']

end boot

/-! ## The completion witnesses at the end of the run (amendment A8, Q37) -/

section done
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Iris.BI Iris.ProofMode in
/-- A completion witness names a member of the completed voters' list, kept. -/
theorem bootDone_mem_keep (tn : TraceNames) (Dn : List w64) (i : w64) :
    (monoListAuthOwn tn.dn 1 Dn ∗ bootDone tn i : IProp GF) ⊢
      (monoListAuthOwn tn.dn 1 Dn ∗ bootDone tn i) ∗ ⌜i ∈ Dn⌝ := by
  refine (and_intro .rfl ?_).trans persistent_and_sep.1
  iintro ⟨Ha, Hd⟩
  iunfold bootDone at Hd
  icases Hd with ⟨%k, Hd⟩
  icases mono_list_auth_idx_lookup tn.dn 1 Dn k i $$ Ha Hd with %h
  ipureintro
  exact List.mem_of_getElem? h

open Iris.BI Iris.ProofMode in
/-- Completion witnesses of the voters `C` name members of the completed voters' list. -/
theorem bootDones_mem (tn : TraceNames) (Dn : List w64) :
    ∀ C : List w64, (monoListAuthOwn tn.dn 1 Dn ∗ ([∗list] i ∈ C, bootDone tn i) : IProp GF) ⊢
      monoListAuthOwn tn.dn 1 Dn ∗ ⌜∀ i ∈ C, i ∈ Dn⌝ := by
  intro C
  induction C with
  | nil =>
    iintro ⟨Ha, -⟩
    iframe Ha
    ipureintro
    intro i hi; cases hi
  | cons x C ih =>
    iintro ⟨Ha, Hs⟩
    icases (BigSepL.bigSepL_cons (Φ := fun _ i => bootDone (GF := GF) tn i)).1 $$ Hs with ⟨Hx, Hs⟩
    icases ih $$ [Ha Hs] with ⟨Ha, %h⟩
    · iframe Ha Hs
    icases bootDone_mem_keep tn Dn x $$ [Ha Hx] with ⟨⟨Ha, -⟩, %hx⟩
    · iframe Ha Hx
    iframe Ha
    ipureintro
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hx
    · exact h i hi

open Iris.BI Iris.ProofMode in
/-- **The simulation's invariant at the end of a run, every voter's bootstrap complete** (amendment A8,
Q37): with the recorder's half of the trace `L` and every voter's completion witness (`bootDone`),
`newTrace` of the run's events succeeds, its initial state the simulation's `simInit C` and its servers
and initial servers the voters' (what `simRun_runAccepted` needs). -/
theorem simInv_end_bootDone (C : List w64) (tn : TraceNames) (Fx : Etcdraft.State → IProp GF)
    (L : List TraceEv) (hC0 : C ≠ []) (hCl : C.length < 2 ^ 40) :
    traceAuth tn.tr L ∗ simInv C tn Fx ∗ ([∗list] i ∈ C, bootDone tn i) ⊢
      traceAuth tn.tr L ∗ simInv C tn Fx ∗
        ⌜∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.init = simInit C ∧ t.server = confAbs C ∧
          t.initSrv = confAbs C⌝ := by
  iintro ⟨Ha, Hi, Hs⟩
  iunfold simInv at Hi
  icases Hi with ⟨%L', %σ, %A, %B, %phP, %phM, %Bt, %Dn, HL, HA, HB, HBt, HDn, Hfx, %Hp⟩
  icases trace_agree_keep tn.tr L L' $$ [Ha HL] with ⟨⟨Ha, HL⟩, %hLL⟩
  · iframe
  subst hLL
  icases bootDones_mem tn Dn C $$ [HDn Hs] with ⟨HDn, %hin⟩
  · iframe HDn Hs
  isplitl [Ha]; · iexact Ha
  isplitl [HL HA HB HBt HDn Hfx]
  · iunfold simInv
    iexists L, σ, A, B, phP, phM, Bt, Dn
    iframe HL HA HB HBt HDn Hfx
    ipureintro; exact Hp
  ipureintro
  obtain ⟨hrun, -, -, -, -, -, -, -, -, -, hev, hseg, hdn⟩ := Hp
  obtain ⟨t, hnt, hsrv, hisrv, hinit⟩ :=
    newTrace_simInit C L σ hC0 hCl hrun hev hseg (fun i hi => hdn i (hin i hi))
  exact ⟨t, hnt, hinit, hsrv, hisrv⟩

end done

end TraceSim

end EtcdGrove
end Perennial
