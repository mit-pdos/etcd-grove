/-
Lean-first (no Rocq counterpart). Trace-check's S7 (part 2) (2026-11-11; `notes/decisions.md`, "S7
(part 2)"): **the traced node API as a client sees it**, an API module (`etc/api/raft.txt`).

The frozen Draft of the gated node API (`TracedApiDraft.lean`: `startTrace`, `StartNode.gatedSpec`,
`Cluster.traceSimInv` and its laws) publicly imports raft's internals (`TracedCap`, through it
`InvRaftPhys`), so a client cannot import it (`etc/api-check.py`). This module imports it privately
and gives the client what the harness (`examples/raft/tracecheck`, `RunConcurrent`) states its proof
in: the simulation's invariant sealed again (`Cluster.traceSim`, the Draft's `Cluster.traceSimInv`), the
gate's precondition over it (`startTraceC`, the Draft's `startTrace`), its two laws (`_alloc`, `_end`),
and the statements of the traced node API that are not proved yet, as `Prop`s the harness takes as
hypotheses:

- `StartNode.tracedSpec D`: `StartNode.gatedSpec` over `startTraceC`, its post also giving the voter's
  `D tn id` (`startDone`): the per-voter "bootstrap complete" fact amendment A7 is to provide (Q37;
  `D := fun _ _ => True` is today's gated statement, `StartNode.tracedSpec_of_gated`,
  `TracedNodeApiBridge.lean`);
- `isReadyChan_recvAu.tracedSpec`: the law `isReadyChan_recvAu` with each of the `Ready`'s messages
  carrying its token (`readyGotT`: `readyGot` and `trTok` of each message; the node API slices'
  `recvTokOf` from `Ready`, `trCap_fire_ready`, `readyToks_queues`);
- `node.Step.tracedSpec`: `node.Step.spec` with `stepIn_intro`'s premises inlined and the message's
  token (`trTok`), which the traced receive line consumes.

Untraced (`Cluster.trace γ = none`) each says what the current statement says (`trTok` is `True`).
The other node-API functions the harness calls (`Tick`, `Advance`, `ApplyConfChange`, `Propose`,
`ReportUnreachable`, `ReportSnapshot`, `Stop`, `Status`) keep their statements: their traced content
is internal to the node (`node.run`'s, inside `isNode`).
-/
module

public import Spec.go_etcd_io.raft.v3.StartNode
public import Proof.go_etcd_io.raft.v3.TraceSimGhost
public import Proof.go_etcd_io.raft.v3.TraceSimEnd
public import Proof.go_etcd_io.raft.v3.InvTrace
import Proof.go_etcd_io.raft.v3.TracedApiDraft
import Proof.go_etcd_io.raft.v3.TracedRecvTok

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

/-! ## The simulation's invariant and the gate's precondition -/

/-- **The simulation's invariant of a traced cluster `γ`** (the voters `vs`, the trace's names `tn`):
the Draft's `Cluster.traceSimInv`, sealed. Its laws: persistent, allocated at the start
(`Cluster.traceSim_alloc`), opened at the end of the run (`Cluster.traceSim_end`). -/
@[no_expose] def Cluster.traceSim (γ : Cluster) (vs : List w64) (tn : TraceNames) : IProp GF :=
  Cluster.traceSimInv γ vs tn

instance Cluster.traceSim_persistent (γ : Cluster) (vs : List w64) (tn : TraceNames) :
    Persistent (Cluster.traceSim (GF := GF) γ vs tn) := by
  unfold Cluster.traceSim; infer_instance

/-- **What a node brings of the trace to `StartNode`**: the Draft's `startTrace` (word for word, over
`Cluster.traceSim`). -/
def startTraceC (γ : Cluster) (vs : List w64) (cv : Config) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(⌜cv.TraceLogger' = interface.nil⌝)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗
      ⌜(cv.PreVote' = false ∧ cv.CheckQuorum' = false) ∧ tn.voters = vs ∧ vs.length < 2 ^ 40 ∧
        cv.TraceLogger' ≠ interface.nil⌝ ∗
      isTraceLogger tn.tr cv.TraceLogger' ∗ Cluster.traceSim γ vs tn ∗
      simNode tn cv.ID' (toC (confAbs vs) ((simInit vs).s (idAbs cv.ID'))) [] ∗
      simBoot tn cv.ID' false none)

/-- **What `StartNode` returns of the trace** (the per-voter fact `D`, amendment A7's Q37): nothing
untraced; traced, `D` at the cluster's names. -/
def startDone (γ : Cluster) (D : TraceNames → w64 → IProp GF) (id : w64) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(True)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ D tn id)

/-- **`StartNode` of a traced cluster** (a hypothesis of the harness until the traced `StartNode` is
proved): `StartNode.gatedSpec` (`TracedApiDraft.lean`) over `startTraceC`, its post also giving
`startDone γ D cv.ID'`. -/
abbrev StartNode.tracedSpec (D : TraceNames → w64 → IProp GF) : Prop :=
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
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ startTraceC γ vs cv }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (K : GName), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        nodeStartedFresh n γ N vs ctxs cv.ID' ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si) K) ∗
        nodeConfig n γ N ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
        nodeRunning n γ N 1 ∗ Q ∗ F K ∗ peers ↦*{dq} pv ∗ startDone γ D cv.ID' }}

omit [StorageModel GF] sem package_sem in
/-- The empty bag represents the empty list. -/
theorem traceSim_bagRep_nil : BagRep [] [] :=
  ⟨List.nodup_nil, fun _ h => by simp at h, fun _ => rfl⟩

/-- **The simulation's invariant at the start** (the Draft's `Cluster.traceSimInv_alloc`): once the
cluster is allocated (any voter's `nodeBoot`), the trace's fragment, the shares' map at the bootstrap
servers with nothing pending, no message handed out and every voter's flag unset. -/
theorem Cluster.traceSim_alloc (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (tn : TraceNames) (A : GMap w64 (ServerC × List Etcdraft.Msg))
    (Bt : GMap w64 (Bool × Option TraceEv)) (E : CoPset) (hE : ↑N ⊆ E)
    (hA : ∀ i ∈ vs, A !! i = some (toC (confAbs vs) ((simInit vs).s (idAbs i)), []))
    (hA' : ∀ i, i ∉ vs → A !! i = none) (hBt : ∀ i ∈ vs, Bt !! i = some (false, none)) :
    (nodeBoot γ N vs ctxs id ∗ traceFrag tn.tr [] ∗ ghostMapAuth tn.st 1 A ∗
        ghostMapAuth tn.bag 1 (∅ : GMap Nat Etcdraft.Msg) ∗ ghostMapAuth tn.bt 1 Bt : IProp GF) ={E}=∗
      Cluster.traceSim γ vs tn := by
  unfold Cluster.traceSim
  exact Cluster.traceSimInv_alloc γ N vs ctxs id tn A Bt E hE hA hA' hBt

/-- **The simulation's invariant at the end of a run** (the Draft's `Cluster.traceSimInv_end`). -/
theorem Cluster.traceSim_end (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E) :
    (nodeBoot γ N vs ctxs id ∗ Cluster.traceSim γ vs tn ∗ traceAuth tn.tr L : IProp GF) ={E}=∗
      traceAuth tn.tr L ∗ ⌜∃ σ, SimRun vs L σ ∧ σ.server = confAbs vs ∧ SimEvents vs.length L⌝ := by
  unfold Cluster.traceSim
  exact Cluster.traceSimInv_end γ N vs ctxs id tn L E hE

/-! ## The messages' tokens -/

/-- **A sent message's token** (gated): untraced, nothing; traced, the token of its specification
message in flight (`recvTokOf`), which `Ready` hands out with the message and the traced receive line
consumes. Sealed: a client only carries it from `Ready` to `node.Step`. -/
@[no_expose] def trTok (γ : Cluster) (st : MsgSt) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(True)
  | some γd => recvTokOf γd st.msg st.ents st.ctx

/-- An untraced cluster's tokens are free. -/
theorem trTok_untraced (γ : Cluster) (st : MsgSt) (h : Cluster.trace γ = none) :
    ⊢ trTok (GF := GF) γ st := by
  unfold trTok; rw [h]; iintro; ipureintro; trivial

/-- **A received `Ready`, traced** (`readyGot` and, for each of its messages, its token `trTok`). -/
def readyGotT (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState)
    (rd : Ready) : IProp GF :=
  iprop(∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan)
      (ms : List QMsg) (ss : Option (w64 × StateType)),
    committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
    isCommittedLogLb γ (st.delivered ++ ce) ∗
    (∃ rs, readStatesPts rd.ReadStates' rs ∗
      [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
    readyRest γ N id rd st ce es h L ms ss ∗
    readyLeaderMsgs γ N id st ms ss ∗
    readyEnter n γ N id st (st.afterReady ce es h L ss) ms ∗
    deliveredLogLb n γ N (st.afterReady ce es h L ss).delivered ∗
    (⌜phsNext st.hardState h = hsZero⌝ ∨
      committedAtTerm γ N (phsNext st.hardState h).Term' (phsNext st.hardState h).Commit' ∗
      ⌜((st.afterReady ce es h L ss).delivered.length : Int) ≤
        uint.Z (phsNext st.hardState h).Commit'⌝) ∗
    -- the messages' tokens
    [∗list] q ∈ ms, trTok γ q.st)

/-- **Receiving a `Ready` as a channel's receive, traced** (a hypothesis of the harness until the
traced `Ready` is proved): the law `isReadyChan_recvAu` with `readyGotT` for `readyGot`. -/
abbrev isReadyChan_recvAu.tracedSpec : Prop :=
  ∀ (n ch : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState)
    (Φ : Ready → Bool → IProp GF),
  st.handling = none →
  ⊢ isReadyChan (GF := GF) n γ N ch -∗ isNode n γ N id -∗ nodeDriver n γ N st -∗
    ∃ γc : ChanNames, isChan ch γc Ready ∗
      (£ 1 ∗ £ 1 -∗
        ▷ (∀ rd : Ready, readyGotT n γ N id st rd -∗ Φ rd true) -∗
        recvAu γc Ready Φ)

/-- **`node.Step(ctx, m)`, traced** (a hypothesis of the harness until the traced `node.Step` is
proved): `node.Step.spec` at `stepIn_intro`'s premises (a copy of a message node `src` sent, to `id`,
with its credits and its snapshot local to `id`), and the message's token. -/
abbrev node.Step.tracedSpec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (src : w64) (st : MsgSt)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  st.msg.To' = id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      sentMsg γ N src st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      msgCredits γ N st ∗ snapLocalMsg γ id st ∗ trTok γ st }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Step"))
      (Val #(interface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; nodeErrS n γ N cd err }}

end spec

end EtcdGrove
end Perennial
