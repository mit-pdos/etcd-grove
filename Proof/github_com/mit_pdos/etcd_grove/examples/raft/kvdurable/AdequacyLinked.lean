/- Lean-first (no Rocq counterpart).

# The durable store's closed adequacy theorem, linked (2026-11-01)

`raft_kvdurable_adequate`: `Adequacy.lean`'s `kvdurable_adequate_of` applied to the linked result
`raft_kvdurable.wp_Main` (`Link.lean`: `Main`'s proof with every callee's linked, the store's, raft's,
lintest's, porcupine's and `durable`'s). A separate file so that `Adequacy.lean` builds without the
store's proofs.

`raft_kvdurable_robust` (2026-11-17) is the same result as an instance of the generic robustness
statement (`Robustness/Statement.lean`, `Robust`): the program alone on one machine that never
crashes (the store's crashes are the program's own, `Cluster.Crash`, with restarts from the
files), under the same hypotheses on the start state; its conclusion is `goose_adequacy`'s, no
thread stuck and none with an unrecovered panic, which is stronger than
`raft_kvdurable_adequate`'s "no thread has ended in a panic" (a thread still unwinding a panic
that nothing will recover is excluded too).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Link
public import Robustness.Statement

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] durableExts durableExtsSemantics durableExtsInterp durableExts_hasExt

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s linked result at `durableGF` (whose `NaInvG` slot porcupine's results take). -/
theorem kvdurable_wp_Main_durableGF : kdMainSpec := by
  intros
  exact raft_kvdurable.wp_Main

/-- **Porcupine never rejects the durable store's trace** (`kvdurable_adequate_of`,
`Adequacy.lean`, with `Main`'s linked result): every real execution of `kvdurableProgram dir` (the
store package's initialization, then `Main(dir)`, which starts a cluster of random options with its
files in `dir`, runs the randomized linearizability test under configuration changes, leadership
disruptions and crashes with restarts from the files, panics unless porcupine answers `Ok`, and
stops the cluster) from a fresh state with one thread whose files hold none of the replicas' files
in `dir`, of `n < 2^61` steps: the main thread's result, if any, is `#()`; no thread is stuck; no
thread has ended in a panic. -/
theorem raft_kvdurable_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]
    [hLog : log.NewModel] (dir : GoString)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (Hfiles : ∀ i ∈ raft_kvreconf.allIds,
      extLocal durableExt σ.world !! raft_kvdurable.kdFileName dir i = none)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvdurableProgram dir], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  kvdurable_adequate_of kvdurable_wp_Main_durableGF dir σ g Hlctx Hinit Hthreads Hfiles n Hn κs t2
    σ2 Hsteps

/-- **The durable store is robust** (`Robustness.Robust`): the program `kvdurableProgram dir` on
one machine that never crashes (and no machine that does), from a fresh state with one thread
whose files hold none of the replicas' files in `dir`, on any shared state `g`: in every
execution of fewer than `2^61` steps (Perennial's `DistCrashNsteps`), no thread is stuck and none
has an unrecovered panic. `Main` panics unless porcupine answers `Ok` on the trace of its
randomized test under configuration changes, leadership disruptions and crashes with restarts
from the files, so porcupine answers `Ok` in every such execution. -/
theorem raft_kvdurable_robust [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]
    [hLog : log.NewModel] (dir : GoString)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (Hfiles : ∀ i ∈ raft_kvreconf.allIds,
      extLocal durableExt σ.world !! raft_kvdurable.kdFileName dir i = none) :
    Robustness.Robust [] [(kvdurableProgram dir, σ)] g (2 ^ 61) :=
  Robustness.Robust.of_single fun n κs t2 σ2 Hn Hsteps =>
    (kvdurable_unrecovered_of kvdurable_wp_Main_durableGF dir σ g Hlctx Hinit Hthreads Hfiles n Hn
      κs t2 σ2 Hsteps).2

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.raft_kvdurable_adequate
#print axioms Perennial.EtcdGrove.raft_kvdurable_robust
