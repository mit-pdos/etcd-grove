/-
Lean-first (no Rocq counterpart). Trace-check's S7 (part 2) (2026-11-11; `notes/decisions.md`, "S7
(part 2)"): the client API's traced statements (`TracedNodeApi.lean`) from the frozen Draft's
(`TracedApiDraft.lean`). Internal (not importable): the final assembly (a linking file) imports it.

`startTraceC` is the Draft's `startTrace` (`startTraceC_eq`), so `StartNode.gatedSpec` gives
`StartNode.tracedSpec` with no completion fact (`D := fun _ _ => True`): the post's `startDone` is the
precondition's directory, kept (`StartNode.tracedSpec_of_gated`). Once amendment A7 gives `StartNode`'s
post a completion fact (Q37), the bridge gains it.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedNodeApi
public import Proof.go_etcd_io.raft.v3.TracedApiDraft
import all Proof.go_etcd_io.raft.v3.TracedNodeApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The client's precondition is the Draft's. -/
theorem startTraceC_eq (γ : Cluster) (vs : List w64) (cv : Config) :
    startTraceC (GF := GF) γ vs cv = startTrace γ vs cv := by
  unfold startTraceC startTrace Cluster.traceSim TracedConfigOk
  rfl

/-- What `startTraceC` keeps: the directory, traced. -/
theorem startTraceC_done (γ : Cluster) (vs : List w64) (cv : Config) :
    startTraceC (GF := GF) γ vs cv ⊢ startTraceC γ vs cv ∗ startDone γ (fun _ _ => iprop(True)) cv.ID' := by
  unfold startTraceC startDone
  cases Cluster.trace γ with
  | none =>
    iintro H
    iframe H
  | some γd =>
    iintro ⟨%tn, #Hdir, H⟩
    isplitl [H]
    · iexists tn; iframe Hdir H
    iexists tn
    iframe Hdir

/-- **`StartNode.tracedSpec` from the Draft's `StartNode.gatedSpec`**, with no completion fact. -/
theorem StartNode.tracedSpec_of_gated (h : StartNode.gatedSpec (GF := GF)) :
    StartNode.tracedSpec (GF := GF) (fun _ _ => iprop(True)) := by
  intro γ N vs ctxs c cv lok si csm Q F peers dq pv h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h16
  iintro %Φ ⟨#Hpkg, Hc, #Hlog, #Hboot, Hvac, Hau, Hstor, Hp, #Hpc, Hst⟩ HΦ
  icases startTraceC_done γ vs cv $$ Hst with ⟨Hst, Hdone⟩
  ihave Hst : startTrace γ vs cv $$ [Hst]
  · rw [← startTraceC_eq]; iexact Hst
  iapply h γ N vs ctxs c cv lok si csm Q F peers dq pv h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h14 h15 h16 $$ [Hc Hvac Hau Hstor Hp Hst]
  · iframe Hpkg Hc Hlog Hboot Hvac Hau Hstor Hp Hpc Hst
  inext
  iintro %nd ⟨%n, %K, %Hnd, #Hfr, #Hn, Hd, Hcf, Hrun, HQ, HF, Hp⟩
  iapply HΦ
  iexists n, K
  iframe Hfr Hn Hd Hcf Hrun HQ HF Hp Hdone
  ipureintro; exact Hnd

end spec

end EtcdGrove
end Perennial
