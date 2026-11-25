/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).saveDisk(hs, ents)`: a node not dead writes its disk (`disk.save`).
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
abbrev node.saveDisk.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) (d : Loc) (w : AntSim.DurW) (hp : Loc)
    (oh : Option HardStateM) (sl : GoSlice) (els : List Loc) (es : List EntryM), SaveOk w es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ n.[H.node, go!"disk"] ↦□ d ∗ emitOk n ∗ diskOwn d w ∗ hsOptRO hp oh ∗
      sl ↦*□ els ∗ [∗list] p;e ∈ els;es, entRO p e }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"saveDisk")) (Val #hp)) (Val #sl))
  {{ RET #(); emitOk n ∗ diskOwn d (saveW w oh es) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
