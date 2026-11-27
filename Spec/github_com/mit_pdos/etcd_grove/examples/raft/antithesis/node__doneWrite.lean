/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 2: nothing proves `node.doneWrite.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*node).doneWrite(w)` (`work`'s `jobDoneWrite` arm, async): the made write job, held by `work`
(`WorkHole.doneW`): raft's storage takes the write, `n.hs` its `after`; the messages that waited for it
sent (`send` with its `cause`, or batching `b`; on a dead node, nothing sent), a batch's `wrote`; its
storage acknowledgements stepped back (`RawNode.Step`, `RawNode.StoreAck`); then `note("write")`
(batching) or `drainAsync("write")`. Ends drained, no job held.
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
abbrev node.doneWrite.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (v : AntSim.NodeView) (q : Qp)
    (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2H c γ j n v .idle (some (.doneW l)) ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode ∧ γ.mode.Async' = true⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"doneWrite")) (Val #l))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
