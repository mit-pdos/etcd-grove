/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessBase.lean`'s).
`withByRole(ev, by, role)`: the report `ev` with its by and role set; `ev` returned.
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
abbrev withByRole.spec : Prop :=
  ∀ (p : Loc) (ev : AntCheck.Event) (by_ role : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      eventOwn p ev }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.withByRole)) (Val #p)) (Val #by_)) (Val #role))
  {{ RET #p; eventOwn p (withByRoleM ev by_ role) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
