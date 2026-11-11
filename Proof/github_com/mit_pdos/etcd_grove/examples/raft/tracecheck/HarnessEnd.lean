/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 2) (2026-11-11; `notes/decisions.md`,
"S7 (part 2)"): **the end of `RunConcurrent`'s run**: `runOver c` from the recorder, the simulation's
invariant and the voters' bootstrap facts.

`RunOk L` (`MainPure.lean`) at the recorder's half of the trace `L` is `runOk_of_sim`'s: the run and the
events' facts from `Cluster.traceSim_end`, the bootstrap facts (`BootFacts`) from amendment A7, which is
in progress: its form is the hypothesis `BootEnd D` (the simulation's invariant, every voter's
completion fact `D tn i` that `StartNode` returns, `StartNode.tracedSpec D`, and the trace's half give
`BootFacts`). Q36 (A7: `BootFacts` false as `simInit` stands) and Q37 (no anchor for the completion fact)
decide `D` and whether `BootFacts` keeps its statement; the harness's proof uses only `BootEnd D`.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedNodeApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.MainSim
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The bootstrap facts at the end of a run** (amendment A7's, a hypothesis of the harness until A7
lands): with a voter's `nodeBoot`, the simulation's invariant, every voter's completion fact `D tn i`
(`StartNode.tracedSpec D`'s `startDone`) and the trace's half `L`, the bootstrap facts of `L`. -/
def BootEnd (D : TraceNames → w64 → IProp GF) : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (id : w64) (tn : TraceNames)
    (L : List TraceEv) (E : CoPset), ↑N ⊆ E →
  ⊢ nodeBoot (GF := GF) γ N vs ctxs id -∗ Cluster.traceSim γ vs tn -∗ ([∗list] i ∈ vs, D tn i) -∗
    traceAuth tn.tr L ={E}=∗ traceAuth tn.tr L ∗ ⌜BootFacts vs L⌝

/-- **The run's end** (the recorder's half `L`): `RunOk L`, from `Cluster.traceSim_end` and the
bootstrap facts (`runOk_of_sim`), for fewer voters than `numBound`. -/
theorem runOk_at_end (D : TraceNames → w64 → IProp GF) (HD : BootEnd D) (γ : Cluster) (N : Namespace)
    (vs : List w64) (ctxs : List (List w8)) (id : w64) (tn : TraceNames) (L : List TraceEv)
    (E : CoPset) (hE : ↑N ⊆ E) (hC : (vs.length : Int) < Etcdraft.numBound) :
    ⊢ nodeBoot (GF := GF) γ N vs ctxs id -∗ Cluster.traceSim γ vs tn -∗ □ ([∗list] i ∈ vs, D tn i) -∗
      traceAuth tn.tr L ={E}=∗ traceAuth tn.tr L ∗ ⌜RunOk L⌝ := by
  iintro #Hb #Hinv #HD Ha
  imod Cluster.traceSim_end (GF := GF) γ N vs ctxs id tn L E hE $$ [Ha] with ⟨Ha, %Hsim⟩
  · iframe Hb Hinv Ha
  imod HD γ N vs ctxs id tn L E hE $$ Hb Hinv HD Ha with ⟨Ha, %Hbf⟩
  imodintro
  iframe Ha
  ipureintro
  obtain ⟨σ, hrun, -, hev⟩ := Hsim
  exact runOk_of_sim vs L σ hrun hev Hbf hC

/-- **`RunConcurrent`'s post from the end of the run**: the cluster's recorder field, the recorder of
the trace `tn.tr`, and the persistent facts `runOk_at_end` needs give `runOver c`. -/
theorem runOver_intro (D : TraceNames → w64 → IProp GF) (HD : BootEnd D) (c r : Loc) (γ : Cluster)
    (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (id : w64) (tn : TraceNames)
    (hC : (vs.length : Int) < Etcdraft.numBound) :
    ⊢ c.[G.Cluster, go!"rec"] ↦□ r -∗ isSyncRecorder (GF := GF) tn.tr r -∗
      nodeBoot γ N vs ctxs id -∗ Cluster.traceSim γ vs tn -∗ □ ([∗list] i ∈ vs, D tn i) -∗
      runOver c := by
  iintro #Hc #Hr #Hb #Hinv #HDs
  iunfold runOver
  iexists tn.tr, r
  iframe Hc Hr
  iintro %L Ha
  iapply runOk_at_end D HD γ N vs ctxs id tn L ⊤ (fun _ _ => CoPset.mem_full) hC $$ Hb Hinv HDs Ha

end ghost

end TraceCheck
end EtcdGrove
end Perennial
