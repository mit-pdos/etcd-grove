/-
Lean-first (no Rocq counterpart). #33 S4, specs first, part 2 (`notes/antithesis-s4-design.md` §2-§3;
the vocabulary is `HarnessInv.lean`'s).
`(*Cluster).deliver(n, inp)`: `inp` is sent on node `j`'s input channel (a bag of `inputOk`
inputs), unless the run stops first (`c.stop` closed), when it is dropped.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInv

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
abbrev Cluster.deliver.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin 3) (inp : H.input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO γ n j ∗ inputOk γ j inp }}
    (App (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"deliver")) (Val #n)) (Val #inp))
  {{ RET #(); True }}

end spec

end AntHarness
end EtcdGrove
end Perennial
