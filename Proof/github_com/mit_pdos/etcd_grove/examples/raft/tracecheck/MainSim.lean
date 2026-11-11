/-
Lean-first (no Rocq counterpart). Trace-check's layers B and D (Q13, 2026-11-09): `Main`'s pure
obligations (`MainPure.lean`, `mainPure`) from the simulation's invariant at the end of the run.

`simInv` keeps the run (`SimRun`) and `Main`'s facts of the events (`SimEvents`: ASCII, in scope, the
bootstrap lines' logs, the numbers below `traceNumBound = 2^61`, the configuration lists within the
number of voters), which
`simInv_end` (`TraceSimEnd.lean`) gives with the recorder's half of the trace. Owed outside the
simulation (hypotheses here):

- that `newTrace` succeeds on the converted events, with the voters' initial state and servers (it
  reads them from the bootstrap lines; `SimRun` alone does not give it, a prefix's lines being read
  with the voters'): `BootFacts`, from complete bootstrap segments (`bootFacts_of_bootDone`; at the end
  of the run, the voters' completion witnesses: `Cluster.traceSim_bootEnd`, amendment A8);
- the number of voters below `numBound` (the cluster's: at most three);
- the event count, `L.length < numBound`: the trace is the recorder's, and each event a Go step of
  the run, so the adequacy theorem's step bound (`n < 2^61`) bounds it, through the recorder (which
  holds the trace's authority) rather than the simulation.

(Inside the simulation, the laws' premises are owed by their callers in the Prove phase: raft's
numbers below `traceNumBound` from the time receipts, and a message's (`Msg.NumsBelow`): a sent one's
from the state and the message it answers, a received one's from a fact its send line records (neither
raft's message facts nor the bags carry them today: the bags drop `rejectHint`): `nodeEvOf_ok`,
`ccEvOf_ok`, `sendEvOf_ok`, `TracedCap.lean`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.MainPure
public import Proof.go_etcd_io.raft.v3.TraceSimEnd

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`Main`'s pure obligations from the simulation's run** (`mainPure` at `K = traceNumBound`,
`n = |C|`): the run `SimRun C L σ` and the events' facts `SimEvents |C| L` (what `simInv` keeps), the
bootstrap facts (`newTrace`'s success at `t`, its initial state and servers), the number of voters
and the event count. -/
theorem mainPure_of_sim (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (t : Etcdraft.Trace)
    (hrun : SimRun C L σ) (hev : SimEvents C.length L) (hnt : Etcdraft.newTrace (L.map evConv) = .ok t)
    (hinit : t.init = simInit C) (hsrv : t.server = confAbs C) (hisrv : t.initSrv = confAbs C)
    (hC : (C.length : Int) < Etcdraft.numBound) (hlen : (L.length : Int) < Etcdraft.numBound) :
    (∀ e ∈ L.map evConv, e.Bounded) ∧ ((L.map evConv).length : Int) < Etcdraft.numBound ∧
    Etcdraft.Event.BootLogsOk (L.map evConv) ∧ t.CheckTraceOk true ∧
      (∀ res, Etcdraft.CheckTraceRel t true res → res = { ok := true }) ∧
      Etcdraft.TraceAccepts (L.map evConv) false false := by
  obtain ⟨-, hscope, hboot, hnums, hconf⟩ := hev
  obtain ⟨h1, h2, h3, t', hnt', h4, h5, h6⟩ := mainPure L traceNumBound C.length (Nat.le_refl _) hC
    (simRun_runAccepted C L σ t hrun hnt hinit hsrv hisrv) hscope hnums hlen hconf hboot
  rw [hnt] at hnt'
  cases hnt'
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **The bootstrap facts** (layer B's bootstrap clause, S7 (part 1): the one input of `RunOk` the
simulation's invariant does not keep): the whole trace parses, and its initial state and servers,
which `newTrace` reads from the bootstrap lines, are the voters' (`simInit C`, `confAbs C`). -/
def BootFacts (C : List w64) (L : List TraceEv) : Prop :=
  ∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.init = simInit C ∧ t.server = confAbs C ∧
    t.initSrv = confAbs C

/-- **The harness's post from the simulation's end** (`Cluster.traceSimInv_end`'s facts): the run
`SimRun`, the events' facts `SimEvents |C| L`, the bootstrap facts and fewer voters than `numBound`
give `RunOk L`. -/
theorem runOk_of_sim (C : List w64) (L : List TraceEv) (σ : Etcdraft.State)
    (hrun : SimRun C L σ) (hev : SimEvents C.length L) (hb : BootFacts C L)
    (hC : (C.length : Int) < Etcdraft.numBound) : RunOk L := by
  obtain ⟨t, hnt, hinit, hsrv, hisrv⟩ := hb
  exact ⟨C.length, hC, simRun_runAccepted C L σ t hrun hnt hinit hsrv hisrv, hev⟩

/-- **The bootstrap facts of a run whose voters' bootstrap is complete** (amendment A8, Q36 (a): since
`simInit` gives every id outside the voters the server `newTraceWith` builds for it, `bootJunk`): once
every voter's bootstrap segment is raft's and complete (`BootSegs`, `BootDone`), `BootFacts` holds
(`newTrace_simInit`). (Before A8 it was false of every such run, A7's `not_bootFacts`.) -/
theorem bootFacts_of_bootDone (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hC0 : C ≠ [])
    (hCl : C.length < 2 ^ 40) (hrun : SimRun C L σ) (hev : SimEvents C.length L) (hseg : BootSegs C L)
    (hdone : ∀ i ∈ C, BootDone C L i) : BootFacts C L := by
  obtain ⟨t, hnt, hsrv, hisrv, hinit⟩ := newTrace_simInit C L σ hC0 hCl hrun hev hseg hdone
  exact ⟨t, hnt, hinit, hsrv, hisrv⟩

open Iris.BI Iris.ProofMode in
/-- **`Main`'s pure obligations at the end of the run** (`simInv_end` and `mainPure_of_sim`): with the
recorder's half of the trace `L`, the simulation's invariant gives `NewTrace`'s premises,
`CheckTrace`'s premise on the trace `t`, the verdict and `TraceAccepts` of `L`'s converted events,
given `newTrace`'s success at `t` with the voters' initial state and servers (layer B's bootstrap
clause, owed), the number of voters and the event count. -/
theorem simInv_main (C : List w64) (tn : TraceNames) (Fx : Etcdraft.State → IProp GF) (L : List TraceEv) :
    traceAuth tn.tr L ∗ simInv C tn Fx ⊢
      traceAuth tn.tr L ∗ simInv C tn Fx ∗
        ⌜∀ t, Etcdraft.newTrace (L.map evConv) = .ok t → t.init = simInit C → t.server = confAbs C →
          t.initSrv = confAbs C → (C.length : Int) < Etcdraft.numBound →
          (L.length : Int) < Etcdraft.numBound →
          (∀ e ∈ L.map evConv, e.Bounded) ∧ ((L.map evConv).length : Int) < Etcdraft.numBound ∧
          Etcdraft.Event.BootLogsOk (L.map evConv) ∧ t.CheckTraceOk true ∧
            (∀ res, Etcdraft.CheckTraceRel t true res → res = { ok := true }) ∧
            Etcdraft.TraceAccepts (L.map evConv) false false⌝ := by
  iintro H
  icases simInv_end C tn Fx L $$ H with ⟨Ha, Hi, %Hp⟩
  iframe Ha Hi
  ipureintro
  obtain ⟨σ, hrun, -, hev⟩ := Hp
  intro t hnt hinit hsrv hisrv hC hlen
  exact mainPure_of_sim C L σ t hrun hev hnt hinit hsrv hisrv hC hlen

end ghost

end TraceCheck
end EtcdGrove
end Perennial
