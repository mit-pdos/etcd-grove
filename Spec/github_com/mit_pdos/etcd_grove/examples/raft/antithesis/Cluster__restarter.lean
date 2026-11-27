/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `Cluster.restarter.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*Cluster).restarter()`: until the run stops, a kill (`inKill`) to a random node, then every node
that is down restarted (`restart`); it ends with what it started with (`restarterOwn`, at the same
total `Q`).
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
abbrev Cluster.restarter.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (Q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ restarterOwn c γ Q ∗ threadTok ∗ ⌜γ.mode.Restarts' = true⌝ }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"restarter")) (Val #()))
  {{ RET #(); restarterOwn c γ Q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
