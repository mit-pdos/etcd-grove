/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*Cluster).handle(n, inp)`: the input's client call and its drain (`step`, `propose`,
`readIndex`, `transferLeader`, `campaign`, `unreachable`; the B2/B3 kinds are not delivered,
`inputOk`), from and back to between inputs.
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
abbrev Cluster.handle.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (inp : H.input) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ nodeOwn c γ j n v .idle ∗ inputOk γ j inp ∗ netAdder c γ q ∗ threadTok ∗
      ⌜DrainB1 γ.scope γ.mode⌝ }}
    (App (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"handle")) (Val #n)) (Val #inp))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwn c γ j n v' .idle ∗ netAdder c γ q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
