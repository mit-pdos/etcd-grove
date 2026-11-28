/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*nodeLogger).Infof(format, v...)`: counts an automatic leaving of a joint configuration in its
node's `autoLeft` (in its invariant, `nodeRO`); nothing else (`isLogger`'s contract).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

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
abbrev nodeLogger.Infof.spec : Prop :=
  ∀ (l n : Loc) (format : GoString) (args : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      l.[H.nodeLogger, go!"n"] ↦□ n ∗ inv antLogN (∃ k : w64, n.[H.node, go!"autoLeft"] ↦ k) }}
    (App (App (Val (l @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.nodeLogger.ty @!! go!"Infof")) (Val #format)) (Val #args))
  {{ RET #(); True }}

end spec

end AntHarness
end EtcdGrove
end Perennial
