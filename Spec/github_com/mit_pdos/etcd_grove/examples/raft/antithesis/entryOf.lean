/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessBase.lean`'s).
`entryOf(e, n)` of a normal entry (a conf entry's arm, `changeOf`, is batch B3's): `entOfE e`.
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
abbrev entryOf.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (e : EntryM) (nn : w64), e.Type' = W32 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      entPts p dq e }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entryOf)) (Val #p)) (Val #nn))
  {{ (g : AntCheck.G.Entry), RET #g; entPts p dq e ∗ AntCheck.entryRO g (entOfE e) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
