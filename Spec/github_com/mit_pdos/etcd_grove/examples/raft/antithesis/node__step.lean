/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).step(m)` of a message to it in flight (a protocol or a transfer message): its report
made (`msgOf`, the cause cell), `RawNode.Step`, the drain (by `recv`), the cell reset.
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
abbrev node.step.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (q : Qp) (ml : Loc) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ nodeOwn c γ j n v .idle ∗ netAdder c γ q ∗ threadTok ∗ ⌜DrainB1 γ.scope γ.mode⌝ ∗
      ((∃ m : Msg, netMsg γ ml st m ∗ ⌜m.dst = AntSim.nodeId j⌝) ∨
       (∃ x : XMsg, netXMsg γ ml st x ∗ ⌜x.dst = AntSim.nodeId j⌝)) }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"step")) (Val #ml))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwn c γ j n v' .idle ∗ netAdder c γ q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
