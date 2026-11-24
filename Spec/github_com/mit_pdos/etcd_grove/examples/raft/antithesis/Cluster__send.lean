/-
Lean-first (no Rocq counterpart). #33 S4, specs first, part 2 (`notes/antithesis-s4-design.md` §2-§3;
the vocabulary is `HarnessInv.lean`'s).
`(*Cluster).send(m)`: a forwarded proposal is dropped at once (`notes/antithesis-s4-design.md` §7);
any other message is handed to a goroutine of its own (`netWg.Add(1)`, backed by the caller's thread
token, `netAdder`) that delivers it to its destination's input channel after a delay, or drops it
(the loss rate, an isolation, a stopped run). The message (`sendMsg`: owned, with its receiver's
facts) goes to the input (`inputOk`).
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
abbrev Cluster.send.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNames) (ml : Loc) (st : MsgSt) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ netAdder c γ q ∗ threadTok ∗ sendMsg γ ml st }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"send")) (Val #ml))
  {{ RET #(); netAdder c γ q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
