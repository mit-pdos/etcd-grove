/-
Lean-first (no Rocq counterpart). #33 S4, specs first, part 2 (`notes/antithesis-s4-design.md` §2-§3;
the vocabulary is `HarnessInv.lean`'s).
`(*Cluster).reportCause(n)`: if the drain's handled message is not reported yet (the cause cell
holds its report, `causeOwn`), it is recorded (`recv`: the report's atomic update takes the
invariant's step `antSim_recv`) and the view says so (`told`); the cell is `nil` after.
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

/-- The view after `reportCause`: its `recv` reported, if it was pending. -/
def reportedView (v : AntSim.NodeView) : AntSim.NodeView :=
  if v.byE = go!"recv" ∧ v.told = false then { v with told := true } else v

/-- See the file header. -/
abbrev Cluster.reportCause.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin 3) (v : AntSim.NodeView) (cl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO γ n j ∗ n.[H.node, go!"cause"] ↦ cl ∗ causeOwn γ j v cl ∗
      viewFrag γ j v ∗ nodeLive γ j }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"reportCause")) (Val #n))
  {{ RET #(); n.[H.node, go!"cause"] ↦ null ∗ causeOwn γ j (reportedView v) null ∗
      viewFrag γ j (reportedView v) ∗ nodeLive γ j }}

end spec

end AntHarness
end EtcdGrove
end Perennial
