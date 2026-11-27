/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`RunCluster(cfg, mode)`: runs a cluster in a mode within B1's mask (`InScope b1Scope mode`) and
returns it, the run over (`runOver`). Premises: the pacing's (`CfgOk`), the thread bound (the
network's goroutines) and the receipts' (`antRunFits`). The caller's thread token is given back.
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
abbrev RunCluster.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)], antRunFits GF →
  ∀ (cfg : H.Config) (mode : H.Mode), CfgOk cfg → InScope b1Scope mode →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      threadTok }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunCluster)) (Val #cfg)) (Val #mode))
  {{ (c : Loc), RET #c; runOver c b1Scope ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
