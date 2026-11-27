/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*Cluster).run(n)`: node `j`'s goroutine: `start` (the `boot` report, the boot drain), then until
the run stops one input at a time (a tick, or an input from its channel: `handle`), each followed
by its drain. At the stop it gives back its right to report and its network adders' share
(`nodesWg.Done()`, `nodeExit`) and its thread token.
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
abbrev Cluster.run.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ nodeOwn c γ j n v .down ∗ netAdder c γ q ∗ threadTok ∗
      sync.join.ownDone (c.[H.Cluster, go!"nodesWg"]) (nodeExit c γ j q) ∗ ⌜DrainB1 γ.scope γ.mode⌝ }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"run")) (Val #n))
  {{ RET #(); threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
