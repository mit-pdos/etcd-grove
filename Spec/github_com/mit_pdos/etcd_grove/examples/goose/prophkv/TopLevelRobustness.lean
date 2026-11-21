/- Lean-first (no Rocq counterpart).

# `goose/prophkv`: the top-level robustness result, stated

`goose_prophkv_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/goose/prophkv/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.goose.prophkv.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace goose_prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open github_com.mit_pdos.etcd_grove.examples.goose.prophkv

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section program

variable [go_gctx : GoGlobalContext]

/-- **`goose_prophkv_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `goose_prophkv_safe`'s other hypotheses: in every
execution of fewer than `bound` steps no thread is stuck and none has an unrecovered panic, so
`GetAny`'s answer is `"a"` or `"b"` (`Main` panics otherwise). -/
def goose_prophkv_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Assumptions] (σ : state)
    (g : GlobalState) (bound : Nat),
    Robustness.Robust [] [(prog, σ)] g (threads := bound + 1) (bound := bound)

end program
end goose_prophkv
end EtcdGrove
end Perennial

end
