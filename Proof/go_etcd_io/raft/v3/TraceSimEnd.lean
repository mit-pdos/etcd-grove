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
(the recorder's, outside the simulation). (Amendment A7, Q29) The bootstrap segments: `simInv_end_boot`
also gives `BootSegs`, and `newTrace_bootInit` what `NewTrace` computes of complete segments
(`bootInit C`, which is `simInit C` at the voters only: the plan's Q30).
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
  obtain ⟨hrun, hsrv, -, -, -, -, -, -, -, -, hasc, -⟩ := Hp
  exact ⟨σ, hrun, hsrv, hasc⟩

open Iris.BI Iris.ProofMode in
/-- **`simInv_end` with the bootstrap segments** (amendment A7, Q29): also the voters' bootstrap
segments are raft's (`BootSegs`, what `NewTrace` reads of the bootstrap lines). -/
theorem simInv_end_boot (C : List w64) (tn : TraceNames) (Fx : Etcdraft.State → IProp GF) (L : List TraceEv) :
    traceAuth tn.tr L ∗ simInv C tn Fx ⊢
      traceAuth tn.tr L ∗ simInv C tn Fx ∗
        ⌜∃ σ, SimRun C L σ ∧ σ.server = confAbs C ∧ SimEvents C.length L ∧ BootSegs C L⌝ := by
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
  obtain ⟨hrun, hsrv, -, -, -, -, -, -, -, -, hasc, hseg⟩ := Hp
  exact ⟨σ, hrun, hsrv, hasc, hseg⟩

end ghost

/-! ## What `NewTrace` reads of complete bootstrap segments (amendment A7, Q29) -/

section boot
variable [GooseExts]

/-- The server `newTraceWith` builds for an id outside the trace's servers: its term, role, vote, log
size and commit are the trace's first line's (`lines.getD (0 - 1)`, an `InitState`: term 0, a follower,
no vote, an empty log, nothing committed), its configuration empty (no configuration is computed for a
non-server). -/
def bootJunk : Etcdraft.Server :=
  let v : Etcdraft.Server :=
    { currentTerm := 0, state := Etcdraft.follower, votedFor := Etcdraft.nil, lead := Etcdraft.nil,
      log := [], commitIndex := 0, votesResponded := [], votesGranted := [], matchIndex := fun _ => 0,
      pendingConfChangeIndex := 0, config := { incoming := [], outgoing := [], learners := [] },
      durable := default }
  { v with durable := Etcdraft.durableOf v }

/-- **The initial state `newTrace` computes of the traced cluster's trace**: `simInit C` at the voters,
`bootJunk` at every other id (the transcription's `s` is total; TLA+'s is over `Server`). -/
def bootInit (C : List w64) : Etcdraft.State :=
  { simInit C with s := fun i => if i ∈ confAbs C then (simInit C).s i else bootJunk }

/-- **`newTrace` of a trace whose voters' bootstrap segments are raft's and complete** (amendment A7,
Q29): it succeeds, its servers and initial servers are the voters', its initial state `bootInit C`. -/
theorem newTrace_bootInit (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hC0 : C ≠ [])
    (hCl : C.length < 2 ^ 40) (hrun : SimRun C L σ) (hev : SimEvents C.length L) (hseg : BootSegs C L)
    (hdone : ∀ i ∈ C, BootDone C L i) :
    ∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.server = confAbs C ∧ t.initSrv = confAbs C ∧
      t.init = bootInit C :=
  newTrace_of_bootDone C L σ hC0 hCl hrun hev hseg hdone

/-- `bootInit C` is not `simInit C` (they differ outside the voters). -/
theorem bootInit_ne_simInit (C : List w64) : bootInit C ≠ simInit C := by
  intro h
  obtain ⟨i, hidef⟩ : ∃ i : Etcdraft.ID, i = ((confAbs C).foldl (· + ·) 0) + 1 := ⟨_, rfl⟩
  have hi : i ∉ confAbs C := by
    have : ∀ (l : List Nat) (a : Nat), ∀ x ∈ l, x ≤ l.foldl (· + ·) a := by
      intro l
      induction l with
      | nil => simp
      | cons y l ih =>
        intro a x hx
        simp only [List.foldl_cons]
        rcases List.mem_cons.1 hx with rfl | hx
        · have : ∀ (l : List Nat) (b : Nat), b ≤ l.foldl (· + ·) b := by
            intro l; induction l with
            | nil => simp
            | cons z l ih' => intro b; simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_add_right _ _) (ih' _)
          exact Nat.le_trans (Nat.le_add_left _ _) (this l _)
        · exact ih _ x hx
    intro hm
    have h2 := this _ 0 i hm
    rw [hidef] at h2
    exact Nat.not_succ_le_self _ h2
  have := congrArg (fun st : Etcdraft.State => (st.s i).currentTerm) h
  simp only [bootInit, simInit, hi, ↓reduceIte, bootJunk] at this
  cases this

end boot

end TraceSim

end EtcdGrove
end Perennial
