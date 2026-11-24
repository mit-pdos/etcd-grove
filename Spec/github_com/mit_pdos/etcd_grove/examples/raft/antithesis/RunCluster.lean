/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`RunCluster(cfg)`: runs the cluster and returns it, the run over (`runOver`). The premises: the
configuration's (`CfgOk`: three voters; a positive tick, `time.NewTicker`'s; `MaxDelay ≥ 0`, else
`below(uint64(MaxDelay) + 1)` divides by zero), the thread bound (the network's `WaitGroup`
counts a goroutine per message in flight) and the receipts' (`antRunFits`), as the trace check's
`RunConcurrent`. The caller's thread token: the boot drains (`Cluster.drain`) take one, and it is
given back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDefs

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev RunCluster.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)], antRunFits GF →
  ∀ (cfg : H.Config), CfgOk cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      threadTok }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunCluster)) (Val #cfg))
  {{ (c : Loc), RET #c; runOver c ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
