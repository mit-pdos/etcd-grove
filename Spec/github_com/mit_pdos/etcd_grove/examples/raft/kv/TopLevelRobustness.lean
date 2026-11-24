/- Lean-first (no Rocq counterpart).

# `raft/kv`: the top-level robustness results, stated

`raft_kv_porcupine_robust`, `raft_kvN_porcupine_robust`: the example's closed theorems as instances of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states them (to audit); the proofs are in
`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kv/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kv.TopLevelDefs
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section closed

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

variable [go_gctx : GoGlobalContext]

/-- **`raft_kv_porcupine_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `raft_kv_porcupine_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 61` steps no thread is stuck and none has an unrecovered panic. -/
def raft_kv_porcupine_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kv.Assumptions]
    [hLog : log.NewModel] (σ : state) (g : GlobalState),
    Robustness.Robust [] [(kvProgram, σ)] g (threads := 2 ^ 61 + 1)
      (bound := 2 ^ 61)

/-- **`raft_kvN_porcupine_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `raft_kvN_porcupine_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 61` steps no thread is stuck and none has an unrecovered panic. -/
def raft_kvN_porcupine_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kv.Assumptions]
    [hLog : log.NewModel] (k : Nat) (σ : state) (g : GlobalState),
    Robustness.Robust [] [(kvProgramN k, σ)] g (threads := 2 ^ 61 + 1)
      (bound := 2 ^ 61)

end closed
end EtcdGrove
end Perennial

end
