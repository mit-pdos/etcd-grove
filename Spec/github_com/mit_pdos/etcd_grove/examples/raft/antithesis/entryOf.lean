/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`entryOf(e)` of a normal entry (`EntryNormal = 0`; the Go panics on any other, so the premise):
the `check.Entry` value of `entOfE e`.
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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev entryOf.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (e : EntryM), e.Type' = W32 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ entPts p dq e }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entryOf)) (Val #p))
  {{ (g : AntCheck.G.Entry), RET #g; entPts p dq e ∗ AntCheck.entryRO g (entOfE e) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
