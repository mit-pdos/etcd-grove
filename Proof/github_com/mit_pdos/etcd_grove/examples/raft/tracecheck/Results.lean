/-
The trace check's results (`examples/raft/tracecheck`, the closed program of
`notes/trace-validation-plan.md`; `notes/trace-check-design.md` §1). The closed statements are
`notes/trace-check-design.md` §1.2 and §1.3, word for word, each **from one open obligation**,
`HarnessOpen`, with no `sorry`:

* **`HarnessOpen`**: the traced node-API statement the harness's proof still takes
  (`HarnessDefs.lean`, `HarnessApi`): `StartNode.tracedSpec`, at every instance context and storage
  model. Steps 3-5 of the design's §9 (the gated `node.run` and the traced constructors) prove it
  (`StartNode.tracedSpec_of_gated`); nothing else is open. The other traced statements the harness
  uses are proved since implementation step 1 (`stepIn_intro` with the token, `trTok_type`,
  `isReadyChan_recvAu.tracedSpec_proof`, the linked `node.Advance.tracedSpec`, `TracedLinked.lean`).
  When it lands, `HarnessOpen` is a theorem and the two results below lose their `_of`.
* **`raft_tracecheck_safe_of`**: §1.2's `raft_tracecheck_safe` (no execution of the package's
  initialization then `Main()`, of `n + 2 ≤ 2^31` steps, panics or gets stuck; the main thread's
  result is `#()`), given the bootstrap log's facts and premises (`Defs.lean`). Everything `Main`
  calls is proved, over raft's linked results (`Proof/go_etcd_io/raft/v3/Linked.lean`, `Link.lean`)
  and the checker's (`etcdraft/Link.lean`): `Main`, `DefaultCConfig`, `RunConcurrent` (the harness,
  `RunConcurrent.lean`) with its goroutines (`app`, `handleReady`, `send`, the drivers), the
  recorder, `ConvertEvents`, the checker's `NewTrace`, `CheckTrace` and `Result.TLCOK`, the package
  initialization (`Init.lean`, `PkgTable.lean`) and the adequacy (`Adequacy.lean`).
* **`raft_tracecheck_accepts_of`**: §1.3's corollary, `RunConcurrent(defaultCConfig)` composed with
  `tracecheck_Events_traceAccepts` (proved with no hypothesis): once a run is over, `c.Events()`
  returns a trace `L` whose converted events satisfy `TraceAccepts` (the Lean transcription's
  acceptance, TLC's verdict with the invariants of `Traceetcdraft.cfg`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.DefaultCConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__Events
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder__Events
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.ConvertEvents
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__app
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__handleReady
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__send
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__replica
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.below
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder__TraceEvent
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Link
public import Proof.go_etcd_io.raft.v3.Linked
public import Proof.go_etcd_io.raft.v3.TracedLinked
public import Proof.go_etcd_io.raft.v3.Link
public import Proof.context.WithTimeoutBackground
public import Proof.google_golang_org.protobuf.proto.ClonePb
public import Perennial.Proof.sync.Link

@[expose] public section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceCheck

/-! ## The corollary's core: a finished run's trace is accepted -/

section corollary
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- **A finished run's trace is accepted** (see the file header): after `RunConcurrent` (its post,
`runOver c`), `c.Events()` returns a slice holding a trace `L` whose converted events satisfy
`TraceAccepts` (and `L` is the recorder's trace when `Events` reads it). -/
theorem tracecheck_Events_traceAccepts (Hrb : receiptBound GF ≤ 2 ^ 61) (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
        runOver c }}
      (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster.ty
        @!! go!"Events")) (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ L, traceEventsRep sl L ∗
        ⌜Etcdraft.TraceAccepts (L.map TraceSim.evConv) false false⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hrun⟩ HΦ
  iunfold runOver at Hrun
  icases Hrun with ⟨%γt, %r, #Hc, #Hr, Hvs⟩
  iapply (Cluster.Events.wp_proof (SyncRecorder.Events.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock)
    c γt r (fun L => iprop(⌜RunOk L⌝))) $$ [Hvs]
  · iframe Hpkg Hc Hr Hvs
  inext
  iintro %sl ⟨%L, #Hsl, %Hlen, %Hok⟩
  have hlen : (L.length : Int) < Etcdraft.numBound := by
    have := Hlen.lt_of_le Hrb; unfold Etcdraft.numBound; omega
  obtain ⟨-, -, -, -, -, -, -, -, hacc⟩ := mainPure_of_runOk L Hok hlen
  iapply HΦ
  iexists L
  iframe Hsl
  ipureintro; exact hacc

end corollary

/-! ## The open obligation, and the harness linked over it -/

/-- **The open obligation** (see the file header): the traced `StartNode` the harness's proof takes
(`HarnessApi`), at every instance context and storage model, as raft's linked results are stated.
Steps 3-5 of `notes/trace-check-design.md` §9 prove it. -/
abbrev HarnessOpen : Prop :=
  ∀ [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors}
    [HeapGS HasLC.hasLC GF] [go.Semantics] [go_etcd_io.raft.v3.Assumptions] [StorageModel GF],
    HarnessApi (GF := GF)

section harness
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- **The harness, linked** (`RunConcurrent`, its `app`s, `handleReady`, `send`), from the open
obligation and raft's linked results. -/
theorem tc_wp_RunConcurrent (h : HarnessOpen) : RunConcurrent.spec (GF := GF) (hG := hG) := by
  have wp_app : ∀ [MemStorReg GF], Cluster.app.spec (GF := GF) (hG := hG) := by
    intro _
    letI : StorageModel GF := memStorageModel
    intro _
    exact Cluster.app.wp_proof RaftLink.node.wp_Advance_traced
      (Cluster.handleReady.wp_proof RaftLink.wp_IsEmptySnap RaftLink.wp_IsEmptyHardState
        RaftLink.MemoryStorage.wp_Append RaftLink.MemoryStorage.wp_SetHardState
        RaftLink.node.wp_ApplyConfChange raftpb.Entry.wp_GetType raftpb.Entry.wp_GetData
        raftpb.Entry.wp_GetIndex proto.wp_UnmarshalConfChange)
      (Cluster.send.wp_proof Cluster.replica.wp_proof raftpb.Message.wp_GetTo
        raftpb.Message.wp_GetType raftpb.Message.wp_GetFrom context.WithTimeoutBackground.wp_proof
        RaftLink.node.wp_Step RaftLink.node.wp_ReportUnreachable)
      below.wp_proof proto.ClonePb.wp_proof RaftLink.node.wp_Ready RaftLink.node.wp_Tick
  letI : MemStorReg GF := ⟨default⟩
  letI : StorageModel GF := memStorageModel
  intro _
  exact RunConcurrent.wp_proof (fun {_} => h (GF := GF)) wp_app
    (SyncRecorder.TraceEvent.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock) below.wp_proof
    RaftLink.wp_NewMemoryStorage RaftLink.MemoryStorage.wp_InitialState
    RaftLink.MemoryStorage.wp_LastIndex RaftLink.MemoryStorage.wp_FirstIndex
    RaftLink.MemoryStorage.wp_Term RaftLink.MemoryStorage.wp_Entries
    RaftLink.MemoryStorage.wp_Snapshot (fun {_} => RaftLink.node.wp_Propose)
    (fun {_} => RaftLink.node.wp_Stop) strconv.wp_Itoa context.WithTimeoutBackground.wp_proof

/-- **Every run's trace is accepted, from the open obligation** (`raft_tracecheck_accepts`,
`notes/trace-check-design.md` §1.3, given `HarnessOpen`): `RunConcurrent(defaultCConfig)`, from the
package initialized and the premises, returns a cluster `c` on which `c.Events()` returns a slice
holding a trace `L` whose converted events satisfy `TraceAccepts` (TLC's verdict on raft's TLA+
trace specification). -/
theorem raft_tracecheck_accepts_of (h : HarnessOpen) [ThreadBoundLe GF (2 ^ 31)]
    (Hrb : receiptBound GF + 3 ≤ 2 ^ 61) (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
        context.isClosedchanInit ∗ tracecheck.premises boot }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent))
        (Val #defaultCConfig))
    {{ (c : Loc), RET (PairV #c #interface.nil);
        WP (App (Val (c @!! go.GoType.PointerType
            github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster.ty @!! go!"Events"))
            (Val #()))
          {{ v, ∃ (sl : GoSlice) (L : List TraceEv), ⌜v = #sl⌝ ∗ traceEventsRep sl L ∗
                ⌜Etcdraft.TraceAccepts (L.map TraceSim.evConv) false false⌝ }} }} := by
  iintro %Φ ⟨#Hpkg, #Hcc, #Hprem⟩ HΦ
  iapply (tc_wp_RunConcurrent h (tcRunFits.intro Hrb) boot Hbf defaultCConfig workload_defaultCConfig) $$ [Hcc Hprem]
  · iframe Hpkg Hcc Hprem
  inext
  iintro %c Hrun
  iapply HΦ
  iapply (tracecheck_Events_traceAccepts (by omega) c) $$ [Hrun]
  · iframe Hpkg Hrun
  inext
  iintro %sl ⟨%L, #Hsl, %Hacc⟩
  iexists sl, L
  iframe Hsl
  ipureintro; exact ⟨rfl, Hacc⟩

end harness

/-! ## The closed theorem, from the open obligation -/

section closed
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **`Main`'s spec at `tcGF`, from the open obligation**: `Main`'s callees, the harness and the
checker, linked. -/
theorem tcMainSpec_of (h : HarnessOpen) : tcMainSpec := by
  intro hG _ _
  exact Main.wp_proof DefaultCConfig.wp_proof (tc_wp_RunConcurrent h)
    (Cluster.Events.wp_proof (SyncRecorder.Events.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock))
    ConvertEvents.wp_proof Etcdraft.wp_NewTrace Etcdraft.wp_CheckTrace Etcdraft.Result.wp_TLCOK

/-- **The trace check never fails, from the open obligation** (`raft_tracecheck_safe`,
`notes/trace-check-design.md` §1.2, given `HarnessOpen`): every real execution of
`tracecheckProgram` -- the tracecheck package's initialization, then `Main()`: a three-voter raft
cluster run concurrently (`RunConcurrent(DefaultCConfig())`: proposals, drops, delays and
reordering, isolations), its trace converted and checked against raft's TLA+ trace specification
(`CheckTrace(tr, true)`), and a panic unless TLC would accept it -- from a fresh state with one
thread, of `n` steps with `n + 2 ≤ 2^31`, given the bootstrap log's facts and premises, has no
stuck thread and no thread that ended in a panic. -/
theorem raft_tracecheck_safe_of (h : HarnessOpen) [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [hLog : log.NewModel]
    (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot)
    (Hprem : ∀ hG : HeapGS .hasLC tcGF,
      ⊢ tracecheck.premises (GF := tcGF) (hG := heapWith hG lctx) boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n + 2 ≤ 2 ^ 31) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([tracecheckProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  tracecheck_adequate_of (tcMainSpec_of h) boot Hbf Hprem σ g Hlctx Hinit Hthreads n Hn κs t2 σ2
    Hsteps

end closed

#print axioms tracecheck_Events_traceAccepts
#print axioms tc_wp_RunConcurrent
#print axioms raft_tracecheck_accepts_of
#print axioms tcMainSpec_of
#print axioms raft_tracecheck_safe_of

end EtcdGrove
end Perennial
