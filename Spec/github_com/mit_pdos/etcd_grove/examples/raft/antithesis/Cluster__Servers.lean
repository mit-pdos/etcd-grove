/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*Cluster).Servers()`: `check.SetOf(names(c.cfg.Nodes))`, the binding's `Server` (and
`InitVoters`); at `Nodes = 3`, `AntSim.cfg3.server`. (`SetOf`'s premise: fewer than `2^62` names.)
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
abbrev Cluster.Servers.spec : Prop :=
  ∀ (c : Loc) (N : w64), uint.Z N < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ c.[H.Cluster, go!"cfg"].[H.Config, go!"Nodes"] ↦□ N }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"Servers")) (Val #()))
  {{ (u : GoSlice), RET #u; AntCheck.strsRO u (AntCheck.setOf (AntSim.namesL (uint.nat N))) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
