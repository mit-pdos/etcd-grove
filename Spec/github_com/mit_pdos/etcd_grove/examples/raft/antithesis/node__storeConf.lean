/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).storeConf()`: with no snapshot in store, the initial voters' configuration.
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
abbrev node.storeConf.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) (ms : Loc) (γs : MemStorNames) (h : HardStateM)
    (sv : SnapshotM), sv.Metadata'.Index' = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ n.[H.node, go!"store"] ↦ ms ∗ memStorLock ms γs ∗ memStorMeta ms γs h ∗
      memStorFresh ms γs 0 sv }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"storeConf")) (Val #()))
  {{ (cs : Loc), RET #cs; n.[H.node, go!"store"] ↦ ms ∗ memStorMeta ms γs h ∗ memStorFresh ms γs 0 sv ∗
      csPts cs DFrac.discard (ConfStateM.mk ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) [] [] [] false) false }}

end spec

end AntHarness
end EtcdGrove
end Perennial
