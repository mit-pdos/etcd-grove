/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).drain(by)`, synchronous, not parallel, not split, no snapshot (`DrainB1`): from
the loop head, each `Ready` until `HasReady` is false: the `ready` report and its write if the
write or the role changed, each message's `send` report and hand-over, the read states' `read`
reports, the committed entries' `apply` report, `Advance`; the drain's `recv` reported before its
first report. The node ends drained, idle.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

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
abbrev node.drain.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ nodeOwn c γ j n v (.loop net₀ xnet₀ r₁ xs₁) ∗ netAdder c γ q ∗ threadTok ∗
      ⌜DrainB1 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"drain")) (Val #v.byE))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwn c γ j n v' .drained ∗ netAdder c γ q ∗ threadTok ∗
      ⌜v'.byE = v.byE⌝ }}

end spec

end AntHarness
end EtcdGrove
end Perennial
