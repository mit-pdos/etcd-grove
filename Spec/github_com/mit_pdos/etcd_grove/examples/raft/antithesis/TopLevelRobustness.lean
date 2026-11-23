/- Lean-first (no Rocq counterpart).

# `raft/antithesis`: the top-level robustness result, stated

`raft_antithesis_robust`: the example's closed theorem (`raft_antithesis_safe`,
`notes/antithesis-s4-design.md` §1) as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads, no thread is
stuck and none has an unrecovered panic). This file only states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.TopLevelDefs
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section closed

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

variable [go_gctx : GoGlobalContext]

/-- **`raft_antithesis_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes, a fresh Go
process (`Robust`'s premise): in every execution of fewer than `2 ^ 61 - 3` steps along which fewer
than `2 ^ 31` threads are live, no thread is stuck and none has an unrecovered panic. No premise:
the harness's logs start empty and nothing it runs is assumed. The harness runs raft with
proposal forwarding disabled (`DisableProposalForwarding`, `notes/antithesis-s4-design.md` §7: raft's
proved `Step` covers only local proposals; to be re-enabled). -/
def raft_antithesis_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
    (σ : state) (g : GlobalState),
    Robustness.Robust [] [(antithesisProgram, σ)] g (threads := 2 ^ 31)
      (bound := 2 ^ 61 - 3)

end closed
end EtcdGrove
end Perennial

end
