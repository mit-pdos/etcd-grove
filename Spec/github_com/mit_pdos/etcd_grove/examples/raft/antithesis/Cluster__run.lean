/-
Lean-first (no Rocq counterpart). #33 S4, specs first, part 2 (`notes/antithesis-s4-design.md` §2-§3;
the vocabulary is `HarnessInv.lean`'s).
`(*Cluster).run(n)`: node `j`'s goroutine, from between inputs: until the run stops (`c.stop`
closed), one input at a time (a tick, or a message or proposal from its input channel: its
`noteInput`, `antSim_quiet`'s `input`; for a message, its `recv` report made before `Step`, the
cause cell), the `RawNode` call, the input's drain, then idle again (the cause cell reset). At the
stop it gives back its right to report and its network adders' share (`nodesWg.Done()`,
`nodeExit`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInv

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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev Cluster.run.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNames) (n : Loc) (j : Fin 3)
    (v : AntSim.NodeView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO γ n j ∗ nodeOwn c γ j n v .idle ∗ netAdder c γ q ∗ threadTok ∗
      sync.join.ownDone (c.[H.Cluster, go!"nodesWg"]) (nodeExit c γ j q) }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"run")) (Val #n))
  {{ RET #(); True }}

end spec

end AntHarness
end EtcdGrove
end Perennial
