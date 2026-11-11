/-
Lean-first (no Rocq counterpart). Trace-check's S7 (part 2) (2026-11-11; `notes/decisions.md`, "S7
(part 2)"): **the traced node API as a client sees it**, an API module (`etc/api/raft.txt`).

The frozen Draft of the gated node API (`TracedApiDraft.lean`: `startTrace`, `StartNode.gatedSpec`,
`Cluster.traceSimInv` and its laws) publicly imports raft's internals (`TracedCap`, through it
`InvRaftPhys`), so a client cannot import it (`etc/api-check.py`). This module imports it privately
and gives the client what the harness (`examples/raft/tracecheck`, `RunConcurrent`) states its proof
in: the simulation's invariant sealed again (`Cluster.traceSim`, the Draft's `Cluster.traceSimInv`), the
gate's precondition over it (`startTraceC`, the Draft's `startTrace`), its laws (`_alloc`, `_end`, and
(amendment A8) `_bootEnd`, over the voters' completion witnesses `startDone`), and the statements of the
traced node API that are not proved yet, as `Prop`s the harness takes as hypotheses:

- `StartNode.tracedSpec`: `StartNode.gatedSpec` over `startTraceC`, its post giving the voter's completion
  witness `startDone γ id` (amendment A8.3, Q37 (a): sealed over the simulation's `bootDone`; the
  Draft's `startDoneB`, `StartNode.tracedSpec_of_gated`, `TracedNodeApiBridge.lean`);
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

/-- **What `StartNode` returns of the trace** (amendment A8.3, Q37 (a)): nothing untraced; traced, the
voter's completion witness (its bootstrap lines all logged, raft's), which with the others' gives the
trace's initial state at the end of the run (`Cluster.traceSim_bootEnd`). Sealed: a client carries it
from `StartNode` to the end law; it is persistent. -/
@[no_expose] def startDone (γ : Cluster) (id : w64) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(True)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ bootDone tn id)

instance startDone_persistent (γ : Cluster) (id : w64) : Persistent (startDone (GF := GF) γ id) := by
  unfold startDone
  cases Cluster.trace γ <;> infer_instance

/-- **`StartNode` of a traced cluster** (a hypothesis of the harness until the traced `StartNode` is
proved): `StartNode.gatedSpec` (`TracedApiDraft.lean`) over `startTraceC`, its post also giving the
voter's completion witness `startDone γ cv.ID'`. -/
abbrev StartNode.tracedSpec : Prop :=
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
        nodeRunning n γ N 1 ∗ Q ∗ F K ∗ peers ↦*{dq} pv ∗ startDone γ cv.ID' }}

omit [StorageModel GF] sem package_sem in
/-- The empty bag represents the empty list. -/
theorem traceSim_bagRep_nil : BagRep [] [] :=
  ⟨List.nodup_nil, fun _ h => by simp at h, fun _ => rfl⟩

/-- **The simulation's invariant at the start** (the Draft's `Cluster.traceSimInv_alloc`): once the
cluster is allocated (any voter's `nodeBoot`), the trace's fragment, the shares' map at the bootstrap
servers with nothing pending, no message handed out, every voter's flag unset and (amendment A8) no
voter's bootstrap complete. -/
theorem Cluster.traceSim_alloc (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (tn : TraceNames) (A : GMap w64 (ServerC × List Etcdraft.Msg))
    (Bt : GMap w64 (Bool × Option TraceEv)) (E : CoPset) (hE : ↑N ⊆ E)
    (hA : ∀ i ∈ vs, A !! i = some (toC (confAbs vs) ((simInit vs).s (idAbs i)), []))
    (hA' : ∀ i, i ∉ vs → A !! i = none) (hBt : ∀ i ∈ vs, Bt !! i = some (false, none)) :
    (nodeBoot γ N vs ctxs id ∗ traceFrag tn.tr [] ∗ ghostMapAuth tn.st 1 A ∗
        ghostMapAuth tn.bag 1 (∅ : GMap Nat Etcdraft.Msg) ∗ ghostMapAuth tn.bt 1 Bt ∗
        monoListAuthOwn tn.dn 1 ([] : List w64) : IProp GF) ={E}=∗
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

open Iris.ProofMode in
/-- The voters' completion witnesses at the directory's names. -/
private theorem startDones_bootDones (γ : Cluster) (γd : GName) (tn : TraceNames)
    (htr : Cluster.trace γ = some γd) :
    ∀ vs : List w64, (traceDir γd tn ∗ ([∗list] i ∈ vs, startDone γ i) : IProp GF) ⊢
      [∗list] i ∈ vs, bootDone tn i := by
  intro vs
  induction vs with
  | nil =>
    iintro -
    iapply (BigSepL.bigSepL_nil (Φ := fun _ i => bootDone (GF := GF) tn i)).2
    iempintro
  | cons x vs ih =>
    iintro ⟨#Hd, Hs⟩
    icases (BigSepL.bigSepL_cons (Φ := fun _ i => startDone (GF := GF) γ i)).1 $$ Hs with ⟨Hx, Hs⟩
    iapply (BigSepL.bigSepL_cons (Φ := fun _ i => bootDone (GF := GF) tn i)).2
    isplitl [Hx]
    · unfold startDone
      rw [htr]
      icases Hx with ⟨%tn', #Hd', #Hb⟩
      unfold traceDir
      icases dghostVar_agree γd tn DfracDiscarded tn' DfracDiscarded $$ Hd Hd' with %heq
      subst heq
      iexact Hb
    · iapply ih
      iframe Hd Hs

open Iris.ProofMode in
/-- **The bootstrap at the end of a run** (amendment A8.4, Q37 (a); review design-r1's S3: over the
witnesses a client holds): in a traced cluster, with a voter's `nodeBoot`, the trace's names (its
directory), the simulation's invariant, every voter's completion witness (`startDone`, from its
`StartNode`) and the recorder's half of the trace `L`, `newTrace` of the run's events succeeds, its
initial state the simulation's (`simInit vs`) and its servers and initial servers the voters'. -/
theorem Cluster.traceSim_bootEnd (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (γd : GName) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E)
    (htr : Cluster.trace γ = some γd) (hne : vs ≠ []) (hlen : vs.length < 2 ^ 40) :
    (nodeBoot γ N vs ctxs id ∗ traceDir γd tn ∗ Cluster.traceSim γ vs tn ∗
        □ ([∗list] i ∈ vs, startDone γ i) ∗ traceAuth tn.tr L : IProp GF) ={E}=∗
      traceAuth tn.tr L ∗ ⌜∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.init = simInit vs ∧
        t.server = confAbs vs ∧ t.initSrv = confAbs vs⌝ := by
  iintro ⟨#Hb, #Hd, #Hinv, #Hs, Ha⟩
  ihave Hbd := startDones_bootDones γ γd tn htr vs $$ [Hd Hs]
  · iframe Hd Hs
  unfold Cluster.traceSim
  iapply Cluster.traceSimInv_bootEnd γ N vs ctxs id tn L E hE hne hlen
  iframe Hb Hinv Hbd Ha

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
