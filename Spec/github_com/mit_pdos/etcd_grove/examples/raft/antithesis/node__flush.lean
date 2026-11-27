/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `node.flush.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*node).flush()` (`inFlush`): in a batching node, raft's `Ready` for every input since the last
one (sync: `flush`, `net`, `made`, the sends, `wrote`, reads, applies, `Advance`, `note`; async:
`drainAsync("batch")` and the reports' empty write job); nothing otherwise. From and back to between
inputs.
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
abbrev node.flush.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (v : AntSim.NodeView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ netAdder c γ.toAntNames q ∗ threadTok ∗ ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"flush")) (Val #()))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .idle ∗ netAdder c γ.toAntNames q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
