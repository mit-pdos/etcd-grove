/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`Name(id)`: the reports' name of node `id`, `AntSim.nameOf id` (`"raft<id>"`, `""` for `0`).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- See the file header. -/
abbrev Name.spec : Prop :=
  ∀ (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name)) (Val #id))
  {{ RET #(AntSim.nameOf id); True }}

end spec

end AntHarness
end EtcdGrove
end Perennial
