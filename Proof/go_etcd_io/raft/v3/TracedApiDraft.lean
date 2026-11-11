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
public import Proof.go_etcd_io.raft.v3.TracedCap
public import Proof.go_etcd_io.raft.v3.TraceSimEnd
import Proof.go_etcd_io.raft.v3.TracedNodeBoot
import all Proof.go_etcd_io.raft.v3.InvNode
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiDec
import Proof.go_etcd_io.raft.v3.InvApiBoot

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

/-- A traced node's configuration (Q6 revision 2, P7): pre-vote and check-quorum off (lifting it
needs 0011's trace logging in the verified raft); `AsyncStorageWrites` is off for every node
already. -/
def TracedConfigOk (cv : Config) : Prop := cv.PreVote' = false ∧ cv.CheckQuorum' = false

/-- **Raft's ghost names of a cluster** (amendment A4; for the package's own statements here):
sealed, as `Cluster.trace` (`Cluster`'s names are the package's; the package's proofs `import all`
this file). -/
@[no_expose] def Cluster.raftNames (γ : Cluster) : RaftNames := ApiImpl.Cluster.raft γ

/-- **The simulation's invariant of a traced cluster `γ`**, the voters `vs`, the trace's names `tn`
(amendment A4, Q20 (a)): the invariant the capability holds (`trCapB`), shared by the cluster's nodes,
inside the cluster's namespace. Sealed (a4-r1's S1: its body is raft's internals, the simulation's
namespace and the specification state's facts `simFx`); its laws: persistent, opened at the end of
the run (`Cluster.traceSimInv_end`); `Cluster.traceSimInv_alloc` is the check that `Main` can allocate
it (on `TraceSimGhost`'s raw ghost maps: the names' allocation law is S7's). -/
@[no_expose] def Cluster.traceSimInv (γ : Cluster) (vs : List w64) (tn : TraceNames) : IProp GF :=
  inv (simNS γ.raftNames) (simInv vs tn (simFx γ.raftNames vs))

instance Cluster.traceSimInv_persistent (γ : Cluster) (vs : List w64) (tn : TraceNames) :
    Persistent (Cluster.traceSimInv (GF := GF) γ vs tn) := by
  unfold Cluster.traceSimInv; infer_instance

/-- What a node brings of the trace to `StartNode`: in an untraced cluster, no logger; in a traced
one, the configuration's premise, the voters the trace's names record and fewer than `2^40` of them
(the bootstrap lines' log, `TraceEv.OkBoot`: raft's bootstrap log has one entry per voter), a logger
that is not nil with the logger's contract for the trace, the simulation's invariant
(`Cluster.traceSimInv`), the node's share at the bootstrap state (`simInit`, nothing pending) and its
`booted` flag unset with no event yet (`simBoot`). (Amendment A4, Q20 (a).) With `nodeBoot` and
`newRaft`'s logger field, the names, the logger, the invariant, the share and the flag make the
capability (`startTrace_trCapB`); the bound is for the bootstrap lines' gates (`TraceEv.OkBoot`), the
configuration's premise for the node's later lines. -/
def startTrace (γ : Cluster) (vs : List w64) (cv : Config) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(⌜cv.TraceLogger' = interface.nil⌝)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗
      ⌜TracedConfigOk cv ∧ tn.voters = vs ∧ vs.length < 2 ^ 40 ∧ cv.TraceLogger' ≠ interface.nil⌝ ∗
      isTraceLogger tn.tr cv.TraceLogger' ∗ Cluster.traceSimInv γ vs tn ∗
      simNode tn cv.ID' (toC (confAbs vs) ((simInit vs).s (idAbs cv.ID'))) [] ∗
      simBoot tn cv.ID' false none)

/-- **What `StartNode` returns of the trace** (amendment A8.3, Q37 (a)): nothing in an untraced cluster;
in a traced one, the node's completion witness `bootDone` at the cluster's trace names (raft logs the
voter's whole bootstrap inside `StartNode`, before `go n.run()`; `trCapB_bootDone` mints the witness at
the end of `setupNode`). -/
def startDoneB (γ : Cluster) (id : w64) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(True)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ bootDone tn id)

/-- **`StartNode`, gated** (Q6 item 1): `StartNode.spec` with its premises `TraceLoggerOk
cv.TraceLogger'` and `Cluster.trace γ = none` replaced by `startTrace` in the precondition (an
untraced cluster's is the first premise, `startTrace_untraced`), its post also giving the node's
completion witness `startDoneB γ cv.ID'` (amendment A8.3). -/
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
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ startTrace γ vs cv }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (K : GName), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        nodeStartedFresh n γ N vs ctxs cv.ID' ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si) K) ∗
        nodeConfig n γ N ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
        nodeRunning n γ N 1 ∗ Q ∗ F K ∗ peers ↦*{dq} pv ∗ startDoneB γ cv.ID' }}

/-- For an untraced cluster, the gated statement is `StartNode.spec`'s: the gate's only content is
the nil logger, `StartNode.spec`'s premise (and the post's `startDoneB` is `True`, `startDoneB_untraced`). -/
theorem startTrace_untraced (γ : Cluster) (vs : List w64) (cv : Config)
    (h : Cluster.trace γ = none) :
    startTrace (GF := GF) γ vs cv ⊣⊢ iprop(⌜TraceLoggerOk cv.TraceLogger'⌝) := by
  unfold startTrace TraceLoggerOk
  rw [h]
  exact .rfl

/-- An untraced cluster's completion witness is `True`. -/
theorem startDoneB_untraced (γ : Cluster) (id : w64) (h : Cluster.trace γ = none) :
    startDoneB (GF := GF) γ id ⊣⊢ iprop(True) := by
  unfold startDoneB; rw [h]; exact .rfl

/-! ## Sufficiency (amendment A4): the capability from `startTrace`, the invariant at the start -/

/-- **`StartNode`'s capability** (amendment A4's check of Q20 (a)): `startTrace` of a traced cluster,
the node's `nodeBoot` (raft's commit log invariant, the node a voter) and `newRaft`'s logger field make
the capability `newRaft` starts with (`trCapB_intro`), unbooted, at the bootstrap share in any phase
`Φ` it satisfies, any `Λ` of no event, for raft's configuration `c` once it holds the voters. -/
theorem startTrace_trCapB (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (cv : Config) (γd : GName) (r : Loc) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop)
    (htr : Cluster.trace γ = some γd) (hc : (elements c.incoming).Perm vs ∧ c.outgoing = ∅)
    (hΦ : Φ vs (toC (confAbs vs) ((simInit vs).s (idAbs cv.ID'))) []) (hΛ : Λ none) :
    (startTrace γ vs cv ∗ nodeBoot γ N vs ctxs cv.ID' ∗ r.[raft, go!"traceLogger"] ↦□ cv.TraceLogger' :
        IProp GF) ⊢
      trCapB (some γd) γ.raftNames r cv.ID' c false Φ Λ := by
  unfold startTrace nodeBoot ApiImpl.nodeBootU ApiImpl.isClusterU ApiImpl.clusterInv raftCommitInv
    Cluster.traceSimInv Cluster.raftNames
  rw [htr]
  iintro ⟨⟨%tn, #Hdir, %Hp, #Hlog, #Hinv, Hnode, Hboot⟩, Hb, #Htl⟩
  obtain ⟨-, hv, -, hnil⟩ := Hp
  icases Hb with ⟨⟨-, ⟨-, ⟨#Hli, -⟩, -⟩, -⟩, %Hpb, -⟩
  iapply trCapB_intro γd tn vs cv.TraceLogger' _ [] none (ApiImpl.Cluster.raft γ) r cv.ID' c Φ Λ
    ⟨hv, hc.1, hc.2, Hpb.1, Nat.le_of_eq Hpb.2.2.2.2.2.2.1.symm⟩ hnil hΦ hΛ
  iframe Hdir Htl Hlog Hinv Hli Hnode Hboot

omit [StorageModel GF] sem package_sem in
/-- The empty bag represents the empty list. -/
theorem bagRep_nil : BagRep [] [] :=
  ⟨List.nodup_nil, fun _ h => by simp at h, fun _ => rfl⟩

/-- **The simulation's invariant at the start** (amendment A4's check of Q20 (a): `Main`'s allocation,
S7): once the cluster is allocated (any voter's `nodeBoot`: raft's commit invariant, the bootstrap
log), the trace's fragment, the shares' map at the bootstrap servers with nothing pending, no message
handed out, every voter's flag unset and no voter's bootstrap complete (amendment A8) go into
`Cluster.traceSimInv`, the facts `simFx` at `simInit` from raft's commit invariant (`simFx_simInit`). -/
theorem Cluster.traceSimInv_alloc (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (tn : TraceNames) (A : GMap w64 (ServerC × List Etcdraft.Msg))
    (Bt : GMap w64 (Bool × Option TraceEv)) (E : CoPset) (hE : ↑N ⊆ E)
    (hA : ∀ i ∈ vs, A !! i = some (toC (confAbs vs) ((simInit vs).s (idAbs i)), []))
    (hA' : ∀ i, i ∉ vs → A !! i = none) (hBt : ∀ i ∈ vs, Bt !! i = some (false, none)) :
    (nodeBoot γ N vs ctxs id ∗ traceFrag tn.tr [] ∗ ghostMapAuth tn.st 1 A ∗
        ghostMapAuth tn.bag 1 (∅ : GMap Nat Etcdraft.Msg) ∗ ghostMapAuth tn.bt 1 Bt ∗
        monoListAuthOwn tn.dn 1 ([] : List w64) : IProp GF) ={E}=∗
      Cluster.traceSimInv γ vs tn := by
  unfold nodeBoot ApiImpl.nodeBootU ApiImpl.isClusterU ApiImpl.clusterInv raftCommitInv
    Cluster.traceSimInv Cluster.raftNames
  iintro ⟨Hb, Hfr, HA, HB, HBt, HDn⟩
  icases Hb with ⟨⟨-, ⟨%HNs, ⟨#Hli, #Hri⟩, -⟩, -⟩, %Hpb, -⟩
  have hN : ↑(raftN (ApiImpl.Cluster.raft γ)) ⊆ E := by
    intro p hp
    unfold raftN at hp; rw [HNs] at hp
    exact hE p (nclose_subseteq N "raft" p hp)
  imod simFx_simInit E (ApiImpl.Cluster.raft γ) vs hN Hpb.2.2.2.2.2.2 $$ [Hli Hri] with #Hfx
  · unfold raftCommitInv; iframe Hli Hri
  iapply inv_alloc
  inext
  iunfold simInv
  iexists [], simInit vs, A, (∅ : GMap Nat Etcdraft.Msg), [], [], Bt, []
  iframe Hfr HA HB HBt HDn Hfx
  ipureintro
  refine ⟨.inl ⟨rfl, rfl⟩, rfl, fun i hi => ⟨[], hA i hi⟩, hA', ?_, ?_, rfl, rfl, ?_, ?_,
    simEvents_nil _, bootSegs_nil _, fun _ h => by cases h⟩
  · have hfl : vs.flatMap (fun i => ((A !! i).map Prod.snd).getD []) = [] := by
      rw [List.flatMap_eq_nil_iff]
      intro i hi
      rw [hA i hi]
      rfl
    rw [hfl]
    exact bagRep_nil
  · simp only [GMap.toList_empty, List.map_nil, List.append_nil]
    exact bagRep_nil
  · intro i hi x hx
    rw [hA i hi] at hx
    simp at hx
  · intro i hi
    refine ⟨false, none, hBt i hi, ?_, ?_, fun h => by simp at h⟩
    · simp [booted]
    · simp [LastOf]

/-- **The simulation's invariant at the end of a run** (a4-r2's S1: the sealed invariant's opening law
for `Main`, `simInv_end`'s): with the recorder's half of the trace `L` and any voter's `nodeBoot` (the
invariant's namespace inside the cluster's `N`), the trace the simulation ran is `L`, from `simInit vs`,
and its events have `Main`'s facts (`SimEvents`, for `simInv_main`'s `mainPure`). -/
theorem Cluster.traceSimInv_end (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E) :
    (nodeBoot γ N vs ctxs id ∗ Cluster.traceSimInv γ vs tn ∗ traceAuth tn.tr L : IProp GF) ={E}=∗
      traceAuth tn.tr L ∗ ⌜∃ σ, SimRun vs L σ ∧ σ.server = confAbs vs ∧ SimEvents vs.length L⌝ := by
  unfold nodeBoot ApiImpl.nodeBootU ApiImpl.isClusterU ApiImpl.clusterInv
    Cluster.traceSimInv Cluster.raftNames
  iintro ⟨Hb, #Hinv, Ha⟩
  icases Hb with ⟨⟨-, ⟨%HNs, -⟩, -⟩, -⟩
  have hsub : ↑(simNS (ApiImpl.Cluster.raft γ)) ⊆ E := by
    intro p hp
    unfold simNS raftN at hp; rw [HNs] at hp
    exact hE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "tracesim" p hp))
  iinv Hinv with >Hi Hclose
  icases simInv_end vs tn _ L $$ [Ha Hi] with ⟨Ha, Hi, %Hp⟩
  · iframe Ha Hi
  imod Hclose $$ [Hi] with -
  · inext; iexact Hi
  imodintro
  iframe Ha
  ipureintro; exact Hp

/-- **The simulation's invariant at the end of a run, every voter's bootstrap complete** (amendment A8.4,
the Draft's form of `Cluster.traceSim_bootEnd`): with the recorder's half of the trace `L` and every
voter's completion witness, `newTrace` of the run's events succeeds at the voters' initial state
(`simInit vs`) and servers (`simInv_end_bootDone`). -/
theorem Cluster.traceSimInv_bootEnd (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E) (hne : vs ≠ [])
    (hlen : vs.length < 2 ^ 40) :
    (nodeBoot γ N vs ctxs id ∗ Cluster.traceSimInv γ vs tn ∗ ([∗list] i ∈ vs, bootDone tn i) ∗
        traceAuth tn.tr L : IProp GF) ={E}=∗
      traceAuth tn.tr L ∗ ⌜∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.init = simInit vs ∧
        t.server = confAbs vs ∧ t.initSrv = confAbs vs⌝ := by
  unfold nodeBoot ApiImpl.nodeBootU ApiImpl.isClusterU ApiImpl.clusterInv
    Cluster.traceSimInv Cluster.raftNames
  iintro ⟨Hb, #Hinv, Hs, Ha⟩
  icases Hb with ⟨⟨-, ⟨%HNs, -⟩, -⟩, -⟩
  have hsub : ↑(simNS (ApiImpl.Cluster.raft γ)) ⊆ E := by
    intro p hp
    unfold simNS raftN at hp; rw [HNs] at hp
    exact hE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "tracesim" p hp))
  iinv Hinv with >Hi Hclose
  icases simInv_end_bootDone vs tn _ L hne hlen $$ [Ha Hi Hs] with ⟨Ha, Hi, %Hp⟩
  · iframe Ha Hi Hs
  imod Hclose $$ [Hi] with -
  · inext; iexact Hi
  imodintro
  iframe Ha
  ipureintro; exact Hp

end spec

end EtcdGrove
end Perennial
