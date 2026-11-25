/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*Cluster).send(m)`: a forwarded proposal is dropped at once unless the mode forwards it; any
other message is handed to a goroutine of its own (`netWg.Add(1)`, `netAdder`) that delivers it
`0 … MaxDeliveries` times to its destination (each a clone: `inputOk`), and, delivered no time,
reports it unreachable to its sender (`inUnreachable`); a snapshot's fate only with `SnapStatus`
(batch B3's).
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
abbrev Cluster.send.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNames) (ml : Loc) (st : MsgSt) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ netAdder c γ q ∗ threadTok ∗ sendMsg γ ml st ∗ ⌜γ.mode.SnapStatus' = false⌝ }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"send")) (Val #ml))
  {{ RET #(); netAdder c γ q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
