/- Lean-first (no Rocq counterpart).

# The reconfiguring store's closed adequacy theorem, linked (2026-10-30, kvreconf-final)

`kvreconf_adequate`: `Adequacy.lean`'s `kvreconf_adequate_of` applied to the linked result
`kvreconf.wp_Main` (`Link.lean`: `Main`'s proof with every callee's linked, the store's, raft's,
lintest's and porcupine's). A separate file so that `Adequacy.lean` builds without the store's
proofs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s linked result at `kvrGF` (whose `NaInvG` slot porcupine's results take). -/
theorem kvreconf_wp_Main_kvrGF : kvrMainSpec := by
  intros
  exact kvreconf.wp_Main

/-- **Porcupine never rejects the reconfiguring store's trace** (`kvreconf_adequate_of`,
`Adequacy.lean`, with `Main`'s linked result): every real execution of `kvreconfProgram` (the store
package's initialization, then `Main()`, which starts a cluster of random options, runs the
randomized linearizability test under configuration changes and leadership disruptions, panics
unless porcupine answers `Ok`, and stops the cluster) from a fresh state with one thread, of
`n < 2^63` steps: the main thread's result, if any, is `#()`; no thread is stuck; no thread has
ended in a panic. -/
theorem kvreconf_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
    [hLog : log.NewModel]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvreconfProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  kvreconf_adequate_of kvreconf_wp_Main_kvrGF σ g Hlctx Hinit Hthreads n Hn κs t2 σ2 Hsteps

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.kvreconf_adequate
