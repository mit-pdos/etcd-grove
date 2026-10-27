/- Lean-first (no Rocq counterpart).

# The store's closed adequacy theorem, linked (2026-10-19)

`kv_adequate`: `Adequacy.lean`'s `kv_adequate_of` applied to the linked result `kv.wp_Main`
(`Link.lean`: `Main`'s proof with every callee's linked, the store's, raft's, lintest's and
porcupine's). A separate file so that `Adequacy.lean` builds without the store's proofs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s linked result at `kvGF` (whose `NaInvG` slot porcupine's results take). -/
theorem kv_wp_Main_kvGF : kvMainSpec := by
  intros
  exact kv.wp_Main

/-- **Porcupine never rejects the store's trace** (`kv_adequate_of`, `Adequacy.lean`, with
`Main`'s linked result): every real execution of `kvProgram` (the store package's
initialization, then `Main()`, which starts the 3-node raft cluster, runs the randomized
linearizability test and panics unless porcupine answers `Ok`) from a fresh state with one
thread, of `n < 2^63` steps: the main thread's result, if any, is `#()`; no thread is stuck; no
thread has ended in a panic. -/
theorem kv_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
    [hErr : context.ErrorStringIsError] [hDE : context.DeadlineExceededIsError]
    [hLog : log.NewModel]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  kv_adequate_of kv_wp_Main_kvGF σ g Hlctx Hinit Hthreads n Hn κs t2 σ2 Hsteps

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.kv_adequate
