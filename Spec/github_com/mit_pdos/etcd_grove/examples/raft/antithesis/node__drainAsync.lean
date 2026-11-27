/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `node.drainAsync.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*node).drainAsync(by)`: raft's `Ready`s with AsyncStorageWrites until there is none: per `Ready`,
the `mem` report (unless batching), the write job queued (its enter promise, its responses, the
`MsgVote`s held until it is made: E1), the apply job queued, the other messages sent (`send` with
`cause`, or batching `b`), the read states.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev node.drainAsync.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v (.loop net₀ xnet₀ r₁ xs₁) ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode ∧ γ.mode.Async' = true⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"drainAsync")) (Val #v.byE))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = v.byE⌝ }}

end spec

end AntHarness
end EtcdGrove
end Perennial
