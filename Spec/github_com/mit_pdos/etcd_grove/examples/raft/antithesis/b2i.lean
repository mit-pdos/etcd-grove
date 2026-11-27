/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `b2i.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`b2i(b)`: `1` for true, `0` for false.
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
abbrev b2i.spec : Prop :=
  ∀ (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.b2i)) (Val #b))
  {{ RET #(W64 (if b then 1 else 0)); True }}

end spec

end AntHarness
end EtcdGrove
end Perennial
