/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `Cluster.restart.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*Cluster).restart(n)`: under the `mu` lock, if node `j` is down, its deposited state taken out
(`downInvB2`), `nodesWg.Add(1)` by the restarter's adder (`restarterOwn`), and a new `run` goroutine
started on it with a share split from the restarter's.
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
abbrev Cluster.restart.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (ns : List Loc) (Q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ clusterRO c ns γ.mode ∗ ⌜ns[j.val]? = some n⌝ ∗ restarterOwn c γ Q ∗ threadTok }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"restart")) (Val #n))
  {{ RET #(); restarterOwn c γ Q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
