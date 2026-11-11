/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 2) (2026-11-11; `notes/decisions.md`,
"S7 (part 2)"): **the end of `RunConcurrent`'s run**: `runOver c` from the recorder, the simulation's
invariant and the voters' bootstrap facts.

`RunOk L` (`MainPure.lean`) at the recorder's half of the trace `L` is `runOk_of_sim`'s: the run and the
events' facts from `Cluster.traceSim_end`, the bootstrap facts (`BootFacts`) from the voters' completion
witnesses (`startDone`, each voter's `StartNode.tracedSpec`) by `Cluster.traceSim_bootEnd` (amendment
A8, Q36 (a), Q37 (a)): `bootEnd`.
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

/-- **The bootstrap facts at the end of a run** (amendment A8.4; A7's hypothesis `BootEnd`, now proved):
in the traced cluster of the directory `γd`, with a voter's `nodeBoot`, the trace's names, the
simulation's invariant, every voter's completion witness (`startDone`, from its `StartNode`) and the
trace's half `L`, the bootstrap facts of `L`. -/
theorem bootEnd (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (id : w64)
    (γd : GName) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E)
    (htr : Cluster.trace γ = some γd) (hne : vs ≠ []) (hlen : vs.length < 2 ^ 40) :
    ⊢ nodeBoot (GF := GF) γ N vs ctxs id -∗ traceDir γd tn -∗ Cluster.traceSim γ vs tn -∗
      □ ([∗list] i ∈ vs, startDone γ i) -∗ traceAuth tn.tr L ={E}=∗ traceAuth tn.tr L ∗ ⌜BootFacts vs L⌝ := by
  iintro #Hb #Hd #Hinv #Hs Ha
  imod Cluster.traceSim_bootEnd (GF := GF) γ N vs ctxs id γd tn L E hE htr hne hlen $$ [Ha]
    with ⟨Ha, %Hbf⟩
  · iframe Hb Hd Hinv Hs Ha
  imodintro
  iframe Ha
  ipureintro
  obtain ⟨t, hnt, hinit, hsrv, hisrv⟩ := Hbf
  exact ⟨t, hnt, hinit, hsrv, hisrv⟩

/-- **The run's end** (the recorder's half `L`): `RunOk L`, from `Cluster.traceSim_end` and the
bootstrap facts (`bootEnd`, `runOk_of_sim`), for fewer voters than `numBound`. -/
theorem runOk_at_end (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (id : w64)
    (γd : GName) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E)
    (htr : Cluster.trace γ = some γd) (hne : vs ≠ []) (hlen : vs.length < 2 ^ 40)
    (hC : (vs.length : Int) < Etcdraft.numBound) :
    ⊢ nodeBoot (GF := GF) γ N vs ctxs id -∗ traceDir γd tn -∗ Cluster.traceSim γ vs tn -∗
      □ ([∗list] i ∈ vs, startDone γ i) -∗ traceAuth tn.tr L ={E}=∗ traceAuth tn.tr L ∗ ⌜RunOk L⌝ := by
  iintro #Hb #Hd #Hinv #Hs Ha
  imod Cluster.traceSim_end (GF := GF) γ N vs ctxs id tn L E hE $$ [Ha] with ⟨Ha, %Hsim⟩
  · iframe Hb Hinv Ha
  imod bootEnd γ N vs ctxs id γd tn L E hE htr hne hlen $$ Hb Hd Hinv Hs Ha with ⟨Ha, %Hbf⟩
  imodintro
  iframe Ha
  ipureintro
  obtain ⟨σ, hrun, -, hev⟩ := Hsim
  exact runOk_of_sim vs L σ hrun hev Hbf hC

/-- **`RunConcurrent`'s post from the end of the run**: the cluster's recorder field, the recorder of
the trace `tn.tr`, and the persistent facts `runOk_at_end` needs give `runOver c`. -/
theorem runOver_intro (c r : Loc) (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (γd : GName) (tn : TraceNames) (htr : Cluster.trace γ = some γd) (hne : vs ≠ [])
    (hlen : vs.length < 2 ^ 40) (hC : (vs.length : Int) < Etcdraft.numBound) :
    ⊢ c.[G.Cluster, go!"rec"] ↦□ r -∗ isSyncRecorder (GF := GF) tn.tr r -∗
      nodeBoot γ N vs ctxs id -∗ traceDir γd tn -∗ Cluster.traceSim γ vs tn -∗
      □ ([∗list] i ∈ vs, startDone γ i) -∗ runOver c := by
  iintro #Hc #Hr #Hb #Hd #Hinv #Hs
  iunfold runOver
  iexists tn.tr, r
  iframe Hc Hr
  iintro %L Ha
  iapply runOk_at_end γ N vs ctxs id γd tn L ⊤ (fun _ _ => CoPset.mem_full) htr hne hlen hC
    $$ Hb Hd Hinv Hs Ha

end ghost

end TraceCheck
end EtcdGrove
end Perennial
