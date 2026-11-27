/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 2: nothing proves `node.doneApply.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*node).doneApply(a)` (`work`'s `jobDoneApply` arm, async): the applied job, held by `work`
(`WorkHole.doneA`): `applying` cleared, `n.applied` its last entry's index (`switchConf` of each: normal
entries, nothing), its storage acknowledgement stepped back (`RawNode.StoreAck`); then `note("apply")`
(batching) or `drainAsync("apply")`. Ends drained, no job held.
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
abbrev node.doneApply.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (v : AntSim.NodeView) (q : Qp)
    (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2H c γ j n v .idle (some (.doneA l)) ∗ netAdder c γ.toAntNames q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode ∧ γ.mode.Async' = true⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"doneApply")) (Val #l))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ netAdder c γ.toAntNames q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
