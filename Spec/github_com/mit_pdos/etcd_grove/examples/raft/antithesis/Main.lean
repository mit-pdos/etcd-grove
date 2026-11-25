/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`Main()`, the closed program: `RunCluster(DefaultConfig(), DrawMode(MainScope()))`, then
`check.Run` of its stream at `c.CheckConfig()`, panicking unless ACCEPTED. It returns (never
panics), under the thread and receipt bounds `RunCluster` takes. (Its proof needs `MainScope()`
within B1's mask: B1's program has `main.go`'s constants at `b1Scope`.)
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
abbrev Main.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)], antRunFits GF →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      threadTok }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end AntHarness
end EtcdGrove
end Perennial
