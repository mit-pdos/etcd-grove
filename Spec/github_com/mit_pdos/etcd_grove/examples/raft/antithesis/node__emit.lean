/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).emit(ev)`: a node that may report (`emitOk`: not dead, no kill due, as in every run
without restarts) records `ev` at its name, firing the caller's update (`reports`), and says so.
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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev node.emit.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) (p : Loc) (ev : AntCheck.Event) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ emitOk n ∗ eventOwn p ev ∗
      reports γ.strm [atNode (AntSim.nameOf (AntSim.nodeId j)) ev] Q }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"emit")) (Val #p))
  {{ RET #true; emitOk n ∗ Q }}

end spec

end AntHarness
end EtcdGrove
end Perennial
