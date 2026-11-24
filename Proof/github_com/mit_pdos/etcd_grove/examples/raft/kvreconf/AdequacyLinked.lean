/- Lean-first (no Rocq counterpart).

# The reconfiguring store's closed adequacy theorem, linked (2026-10-30, kvreconf-final)

`raft_kvreconf_adequate`: `Adequacy.lean`'s `kvreconf_adequate_of` applied to the linked result
`raft_kvreconf.wp_Main` (`Link.lean`: `Main`'s proof with every callee's linked, the store's, raft's,
lintest's and porcupine's). A separate file so that `Adequacy.lean` builds without the store's
proofs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s linked result at `kvrGF` (whose `NaInvG` slot porcupine's results take). -/
theorem kvreconf_wp_Main_kvrGF : kvrMainSpec := by
  intros
  exact raft_kvreconf.wp_Main

/-- **Porcupine never rejects the reconfiguring store's trace** (`kvreconf_adequate_of`,
`Adequacy.lean`, with `Main`'s linked result): every real execution of `kvreconfProgram` (the store
package's initialization, then `Main()`, which starts a cluster of random options, runs the
randomized linearizability test under configuration changes and leadership disruptions, panics
unless porcupine answers `Ok`, and stops the cluster) from a fresh state with one thread, of
`n < 2^61` steps: the main thread's result, if any, is `#()`; no thread is stuck; no thread has
ended in a panic. -/
theorem raft_kvreconf_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]
    [hLog : log.NewModel]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvreconfProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  kvreconf_adequate_of kvreconf_wp_Main_kvrGF σ g Hlctx Hinit Hthreads n Hn κs t2 σ2 Hsteps


/-- `MainN`'s linked result at `kvrGF` (2026-11-16, kvraftN). -/
theorem kvreconf_wp_MainN_kvrGF : kvrMainNSpec := by
  intros
  exact raft_kvreconf.wp_MainN

/-- **Porcupine never rejects the reconfiguring store's trace on `k` voters** (`kvreconfN_adequate_of`,
`Adequacy.lean`, with `MainN`'s linked result; 2026-11-16, kvraftN): every real execution of
`kvreconfProgramN k`, any `k` (the store package's initialization, then `MainN(k)`, which returns at
once unless `1 ≤ k ≤ 1000`, and otherwise starts a cluster of random options on the voters `1 … k`, with up to `k + 4` replicas, runs the randomized
linearizability test under configuration changes and leadership disruptions, panics unless porcupine
answers `Ok`, and stops the cluster) from a fresh state with one thread, of `n < 2^61` steps: the main
thread's result, if any, is `#()`; no thread is stuck; no thread has ended in a panic. -/
theorem raft_kvreconfN_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]
    [hLog : log.NewModel] (k : Nat)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvreconfProgramN k], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  kvreconfN_adequate_of kvreconf_wp_MainN_kvrGF k σ g Hlctx Hinit Hthreads n Hn κs t2 σ2 Hsteps

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.raft_kvreconf_adequate
#print axioms Perennial.EtcdGrove.raft_kvreconfN_adequate
