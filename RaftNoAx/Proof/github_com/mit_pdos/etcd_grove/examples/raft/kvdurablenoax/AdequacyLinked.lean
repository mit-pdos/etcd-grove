-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/AdequacyLinked.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

# The durable store's closed adequacy theorem, linked (2026-11-01)

`raft_kvdurable_adequate`: `Adequacy.lean`'s `kvdurable_adequate_of` applied to the linked result
`raft_kvdurable.wp_Main` (`Link.lean`: `Main`'s proof with every callee's linked, the store's, raft's,
lintest's, porcupine's and `durable`'s). A separate file so that `Adequacy.lean` builds without the
store's proofs.
-/
module

public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Adequacy
public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Link

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
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
    [hLog : log.NewModel] (dir : GoString)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (Hfiles : ∀ i ∈ raft_kvreconf.allIds,
      extLocal durableExt σ.world !! raft_kvdurable.kdFileName dir i = none)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvdurableProgram dir], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  kvdurable_adequate_of kvdurable_wp_Main_durableGF dir σ g Hlctx Hinit Hthreads Hfiles n Hn κs t2
    σ2 Hsteps


/-- `MainN`'s linked result at `durableGF` (2026-11-16, kvraftN). -/
theorem kvdurable_wp_MainN_durableGF : kdMainNSpec := by
  intros
  exact raft_kvdurable.wp_MainN

/-- **Porcupine never rejects the durable store's trace on `k` voters** (`kvdurableN_adequate_of`,
`Adequacy.lean`, with `MainN`'s linked result; 2026-11-16, kvraftN): every real execution of
`kvdurableProgramN dir k`, any `k` (the store package's initialization, then `MainN(dir, k)`, which
returns at once unless `1 ≤ k ≤ 1000`, and otherwise starts a cluster of random options on the voters `1 … k`, with up to `k + 4` replicas and their
files in `dir`, runs the randomized linearizability test under configuration changes, leadership
disruptions and crashes with restarts from the files, panics unless porcupine answers `Ok`, and stops
the cluster) from a fresh state with one thread whose files hold none of the files of the replicas
`1 … k + 4` in `dir`, of `n < 2^61` steps: the main thread's result, if any, is `#()`; no thread is
stuck; no thread has ended in a panic. -/
theorem raft_kvdurableN_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
    [hLog : log.NewModel] (dir : GoString) (k : Nat)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (Hfiles : ∀ i ∈ raft_kvreconf.bootVoters (k + 4),
      extLocal durableExt σ.world !! raft_kvdurable.kdFileName dir i = none)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvdurableProgramN dir k], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  kvdurableN_adequate_of kvdurable_wp_MainN_durableGF dir k σ g Hlctx Hinit Hthreads Hfiles n Hn
    κs t2 σ2 Hsteps

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.raft_kvdurable_adequate
#print axioms Perennial.EtcdGrove.raft_kvdurableN_adequate
