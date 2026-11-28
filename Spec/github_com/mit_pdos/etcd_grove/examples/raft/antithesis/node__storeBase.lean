/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).storeBase()`: the index of the storage's snapshot, `0` (never compacted: batch B3's).
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
abbrev node.storeBase.spec : Prop :=
  ∀ (n ms : Loc) (γs : MemStorNames) (h : HardStateM) (sv : SnapshotM), sv.Metadata'.Index' = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      n.[H.node, go!"store"] ↦ ms ∗ memStorLock ms γs ∗ memStorMeta ms γs h ∗ memStorFresh ms γs 0 sv }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"storeBase")) (Val #()))
  {{ RET #(W64 0); n.[H.node, go!"store"] ↦ ms ∗ memStorMeta ms γs h ∗ memStorFresh ms γs 0 sv }}

end spec

end AntHarness
end EtcdGrove
end Perennial
