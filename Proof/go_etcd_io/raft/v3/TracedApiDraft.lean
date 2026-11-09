/-
Lean-first (no Rocq counterpart). Trace-check's Q6 (`notes/trace-validation-q6.md`, revision 2),
Draft (2026-11-09): the node API's statements with the traced-only premises, gated on the
cluster's `reTrace` (`Cluster.trace`).

Each `X.gatedSpec` here is the current `X.spec` (its file under `Spec/go_etcd_io/raft/v3/`) with
the gate added; for an untraced cluster (`Cluster.trace γ = none`, every existing client's) it says
what `X.spec` says. **Decided by the agent (2026-11-09):** a gated statement replaces its `X.spec`
only once its proof is complete. A `sorry` in `StartNode.wp_proof` (or `Advance`'s, `Step`'s)
would reach every existing closed theorem through it, which the acceptance test (the plan's
"Q6's acceptance test") forbids; until then the statements are definitions here, reviewed with
the rest of the Draft, and the existing specs stay as they are.
-/
module

public import Spec.go_etcd_io.raft.v3.StartNode
public import Proof.go_etcd_io.raft.v3.TraceSimGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 TraceSim

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The namespace of the simulation's invariant (inside the cluster's). -/
def simN (N : Namespace) : Namespace := N .@ "tracesim"

/-- A traced node's configuration (Q6 revision 2, P7): pre-vote and check-quorum off (lifting it
needs 0011's trace logging in the verified raft); `AsyncStorageWrites` is off for every node
already. -/
def TracedConfigOk (cv : Config) : Prop := cv.PreVote' = false ∧ cv.CheckQuorum' = false

/-- What a node brings of the trace to `StartNode`: in an untraced cluster, no logger; in a traced
one, the configuration's premise, the logger's contract for the trace, the simulation's
invariant, and the node's share at the bootstrap state (`simInit`, nothing pending). -/
def startTrace (γ : Cluster) (N : Namespace) (vs : List w64) (cv : Config) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(⌜cv.TraceLogger' = interface.nil⌝)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ ⌜TracedConfigOk cv⌝ ∗
      isTraceLogger tn.tr cv.TraceLogger' ∗ inv (simN N) (simInv vs tn) ∗
      simNode tn cv.ID' (toC (confAbs vs) ((simInit vs).s (idAbs cv.ID'))) [])

/-- **`StartNode`, gated** (Q6 item 1): `StartNode.spec` with its premise `TraceLoggerOk
cv.TraceLogger'` replaced by `startTrace` in the precondition (an untraced cluster's is the same
premise). -/
abbrev StartNode.gatedSpec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk) (csm : ConfStateM) (Q : IProp GF) (F : GName → IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  csm.Voters' = [] → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  vs = pv.map Peer.ID' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      nodeBoot γ N vs ctxs cv.ID' ∗ nodeVacant γ cv.ID' ∗
      AU <{ ∃∃ (S : RaftState), raftState γ cv.ID' S ∗ ⌜S = RaftState.init⌝ }> @ ⊤ \ ↑N, ∅
         <{ raftState γ cv.ID' S, COMM Q }> ∗
      restartStorage γ (interface.ok si) ⟨hsZero, none, entryID.mk (W64 0) (W64 0), []⟩ csm 0 F ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ startTrace γ N vs cv }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (K : GName), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        nodeStartedFresh n γ N vs ctxs cv.ID' ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si) K) ∗
        nodeConfig n γ N ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
        nodeRunning n γ N 1 ∗ Q ∗ F K ∗ peers ↦*{dq} pv }}

/-- For an untraced cluster, the gated statement is `StartNode.spec`'s: the gate's only content is
the nil logger, `StartNode.spec`'s premise. -/
theorem startTrace_untraced (γ : Cluster) (N : Namespace) (vs : List w64) (cv : Config)
    (h : Cluster.trace γ = none) :
    startTrace (GF := GF) γ N vs cv ⊣⊢ iprop(⌜TraceLoggerOk cv.TraceLogger'⌝) := by
  unfold startTrace TraceLoggerOk
  rw [h]
  exact .rfl

end spec

end EtcdGrove
end Perennial
