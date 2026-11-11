/-
The trace check's results (`examples/raft/tracecheck`, the closed program of
`notes/trace-validation-plan.md`; S7 (part 1), 2026-11-11): **a skeleton**. The closed theorem
`raft_tracecheck_safe` (no execution of the package's initialization then `Main()` panics) and its
corollary (the trace of every run satisfies `TraceAccepts`) are not stated here yet: what they
rest on is not all proved. Stated and proved instead, with every open obligation an explicit
hypothesis, no `sorry`:

* **`raft_tracecheck_safe_of`**: the closed theorem's statement (`tracecheck_adequate_of`'s, the
  plan's shape, as `raft_kv_porcupine_safe`: for executions of `n + 4 ≤ 2^61` steps, no stuck
  thread, no panic, the main thread's result `#()`), given
  `TcOpen`, the harness's spec (`Spec/.../tracecheck/RunConcurrent.lean`): the run over the
  traced node API, whose traced statements are being finished (Q8, slice 27n), with layer B's
  bootstrap facts (`MainSim.lean`, `BootFacts`) at its end.
  Everything else `Main` calls is proved: `Main` (`Main.lean`), `DefaultCConfig`,
  `(*Cluster).Events` and the recorder's `Events` (the recorder's time receipts bound the event
  count), `ConvertEvents`, the package initialization (`Init.lean`, `PkgTable.lean`), the
  adequacy (`Adequacy.lean`), and the checker's `NewTrace`, `CheckTrace` and `Result.TLCOK`,
  linked over every checker function they reach (`etcdraft/Link.lean`, `etc/gen-link.py
  --tracecheck`; until the checker's link, S7, 2026-11-11, `TcOpen` also held the six checker
  specs `NewTrace`'s and `CheckTrace`'s proofs take).
* **`tracecheck_Events_traceAccepts`**: the corollary's core, proved with no hypothesis: once a run
  is over (`runOver c`, `RunConcurrent.spec`'s post), `c.Events()` returns a trace `L` whose
  converted events satisfy `TraceAccepts` (the Lean transcription's acceptance, TLC's verdict with
  the invariants of `Traceetcdraft.cfg`).

When `h_RunConcurrent` is proved, `raft_tracecheck_safe` is
`raft_tracecheck_safe_of` with them filled in, and the corollary is `RunConcurrent.spec` composed
with `tracecheck_Events_traceAccepts`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.DefaultCConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__Events
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder__Events
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.ConvertEvents
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Link
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
    unfold Etcdraft.numBound; omega
  obtain ⟨-, -, -, -, -, -, -, -, hacc⟩ := mainPure_of_runOk L Hok hlen
  iapply HΦ
  iexists L
  iframe Hsl
  ipureintro; exact hacc

end corollary

/-! ## The closed theorem, from the open obligations -/

section closed
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The open obligation** (see the file header), at `tcGF`, for every `HeapGS`, semantics and
package assumptions (as `tcMainSpec`): the harness's `RunConcurrent`. (The checker's specs are
linked, `etcdraft/Link.lean`.) -/
abbrev TcOpen : Prop :=
  ∀ [hG : HeapGS HasLC.hasLC tcGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions],
    RunConcurrent.spec (GF := tcGF) (hG := hG)

/-- **`Main`'s spec at `tcGF`, from the open obligation**; the rest of `Main`'s callees are
proved, the checker's linked. -/
theorem tcMainSpec_of (h : TcOpen) : tcMainSpec := by
  intro hG _ _
  exact Main.wp_proof DefaultCConfig.wp_proof h
    (Cluster.Events.wp_proof (SyncRecorder.Events.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock))
    ConvertEvents.wp_proof Etcdraft.wp_NewTrace Etcdraft.wp_CheckTrace Etcdraft.Result.wp_TLCOK

/-- **The trace check never fails, from the open obligations** (`raft_tracecheck_safe`'s statement,
`tracecheck_adequate_of`, given `TcOpen`): every real execution of `tracecheckProgram` -- the
tracecheck package's initialization, then `Main()`: a three-voter raft cluster run concurrently
(`RunConcurrent(DefaultCConfig())`: proposals, drops, delays and reordering, isolations), its trace
converted and checked against raft's TLA+ trace specification (`CheckTrace(tr, true)`), and a panic
unless TLC would accept it -- from a fresh state with one thread, of `n` steps with
`n + 4 ≤ 2^61`, has no stuck thread and no thread that ended in a panic. -/
theorem raft_tracecheck_safe_of [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [hLog : log.NewModel] (hopen : TcOpen)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n + 4 ≤ 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([tracecheckProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  tracecheck_adequate_of (tcMainSpec_of hopen) σ g Hlctx Hinit Hthreads n Hn κs t2 σ2 Hsteps

end closed

#print axioms tracecheck_Events_traceAccepts
#print axioms tcMainSpec_of
#print axioms raft_tracecheck_safe_of

end EtcdGrove
end Perennial
