/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).parts(hs, ents)` without split writes (`Mode.Split = 0`): the one write of the `Ready`:
the hard state if it changed (`nil` otherwise), the entries, the hard state after.
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
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev node.parts.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) (hp hp0 : Loc) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ n.[H.node, go!"hs"] ↦ hp0 ∗ ⌜γ.mode.Split' = W64 0⌝ }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"parts")) (Val #hp)) (Val #sl))
  {{ (out : GoSlice), RET #out; n.[H.node, go!"hs"] ↦ hp0 ∗
      out ↦* [({ hs' := if hp = hp0 then null else hp, ents' := sl, after' := hp } : H.part)] }}

end spec

end AntHarness
end EtcdGrove
end Perennial
