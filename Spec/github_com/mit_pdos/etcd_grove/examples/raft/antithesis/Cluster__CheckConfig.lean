/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessBase.lean`'s).
`(*Cluster).CheckConfig()`: the binding's constants of the run's mode (`Server = names(Nodes)`,
`InitVoters = names(Voters)`, `Bootstrapped`): `R.cfg` for the run's `R` (`ModeRun`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessBase

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
abbrev Cluster.CheckConfig.spec : Prop :=
  ∀ (c : Loc) (m : H.Mode),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      c.[H.Cluster, go!"mode"] ↦□ m ∗ ⌜uint.Z m.Voters' ≤ uint.Z m.Nodes' ∧ uint.Z m.Nodes' ≤ 9⌝ }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"CheckConfig")) (Val #()))
  {{ (p : Loc), RET #p; AntCheck.configRO p
      { server := AntCheck.setOf (AntSim.namesL (uint.nat m.Nodes')),
        initVoters := AntCheck.setOf (AntSim.namesL (uint.nat m.Voters')), bootstrapped := m.Boot' } }}

end spec

end AntHarness
end EtcdGrove
end Perennial
