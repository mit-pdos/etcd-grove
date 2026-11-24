/- Lean-first (no Rocq counterpart).

# The store's closed adequacy theorem, linked (2026-10-19)

`raft_kv_adequate`: `Adequacy.lean`'s `kv_adequate_of` applied to the linked result `raft_kv.wp_Main`
(`Link.lean`: `Main`'s proof with every callee's linked, the store's, raft's, lintest's and
porcupine's). A separate file so that `Adequacy.lean` builds without the store's proofs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kv.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kv.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s linked result at `kvGF` (whose `NaInvG` slot porcupine's results take). -/
theorem kv_wp_Main_kvGF : kvMainSpec := by
  intros
  exact raft_kv.wp_Main

/-- **Porcupine never rejects the store's trace** (`kv_adequate_of`, `Adequacy.lean`, with
`Main`'s linked result): every real execution of `kvProgram` (the store package's
initialization, then `Main()` = `MainN(3)`, which starts the 3-node raft cluster, runs the randomized
linearizability test and panics unless porcupine answers `Ok`) from a fresh state with one
thread, of `n < 2^61` steps: the main thread's result, if any, is `#()`; no thread is stuck; no
thread has ended in a panic. -/
theorem raft_kv_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kv.Assumptions]
    [hLog : log.NewModel]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  kv_adequate_of kv_wp_Main_kvGF σ g Hlctx Hinit Hthreads n Hn κs t2 σ2 Hsteps

/-- `MainN`'s linked result at `kvGF` (2026-11-15, kvraftN). -/
theorem kv_wp_MainN_kvGF : kvMainNSpec := by
  intros
  exact raft_kv.wp_MainN

/-- **Porcupine never rejects the store's trace on `k` replicas** (`kvN_adequate_of`, with
`MainN`'s linked result; 2026-11-15, kvraftN): every real execution of `kvProgramN k`, any `k`
(the store package's initialization, then `MainN(k)`, which returns at once unless `1 ≤ k ≤ 1000`,
and otherwise starts the raft cluster of the voters `1 … k`, runs the randomized linearizability test and panics unless porcupine answers `Ok`)
from a fresh state with one thread, of `n < 2^61` steps: the main thread's result, if any, is
`#()`; no thread is stuck; no thread has ended in a panic. -/
theorem raft_kvN_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kv.Assumptions]
    [hLog : log.NewModel] (k : Nat)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvProgramN k], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  kvN_adequate_of kv_wp_MainN_kvGF k σ g Hlctx Hinit Hthreads n Hn κs t2 σ2 Hsteps

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.raft_kv_adequate
#print axioms Perennial.EtcdGrove.raft_kvN_adequate
