-- The copy for the part `RaftNoAx/` of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/TopLevelRobustness.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

# `raft/kvdurable`: the top-level robustness results, stated

`raft_kvdurable_porcupine_robust`, `raft_kvdurableN_porcupine_robust`: the example's closed theorems as instances of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states them (to audit); the proofs are in
`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/TopLevelRobustness.lean`.
-/
module

public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.TopLevelDefs
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section closed

attribute [local instance] durableExts durableExtsSemantics durableExtsInterp durableExts_hasExt

variable [go_gctx : GoGlobalContext]

/-- **`raft_kvdurable_porcupine_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `raft_kvdurable_porcupine_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 61` steps no thread is stuck and none has an unrecovered panic. -/
def raft_kvdurable_porcupine_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
    [hLog : log.NewModel] (dir : GoString) (σ : state) (g : GlobalState)
    (Hfiles : ∀ i ∈ raft_kvreconf.allIds,
      extLocal durableExt σ.world !! raft_kvdurable.kdFileName dir i = none),
    Robustness.Robust [] [(kvdurableProgram dir, σ)] g (threads := 2 ^ 61 + 1)
      (bound := 2 ^ 61)

/-- **`raft_kvdurableN_porcupine_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `raft_kvdurableN_porcupine_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 61` steps no thread is stuck and none has an unrecovered panic. -/
def raft_kvdurableN_porcupine_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
    [hLog : log.NewModel] (dir : GoString) (k : Nat) (σ : state) (g : GlobalState)
    (Hfiles : ∀ i ∈ raft_kvreconf.bootVoters (k + 4),
      extLocal durableExt σ.world !! raft_kvdurable.kdFileName dir i = none),
    Robustness.Robust [] [(kvdurableProgramN dir k, σ)] g (threads := 2 ^ 61 + 1)
      (bound := 2 ^ 61)

end closed
end EtcdGrove
end Perennial

end
