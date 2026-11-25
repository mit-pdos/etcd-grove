/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).reads(rd)`: each read state of the `Ready` reported (`read`), the handled message's
`recv` first if pending.
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
abbrev node.reads.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) (rd : go_etcd_io.raft.v3.Ready) (rss : List ReadStateM)
    (cl : Loc) (o : Option AntCheck.Event) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ emitOk n ∗ readStatesPts rd.ReadStates' rss ∗ n.[H.node, go!"cause"] ↦ cl ∗
      pendingCause cl o ∗
      reports γ.strm ((if rss = [] then [] else o.toList ++ rss.map readEvM).map
        (atNode (AntSim.nameOf (AntSim.nodeId j)))) Q }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"reads")) (Val #rd))
  {{ RET #(); emitOk n ∗ readStatesPts rd.ReadStates' rss ∗
      (if rss = [] then n.[H.node, go!"cause"] ↦ cl ∗ pendingCause cl o else n.[H.node, go!"cause"] ↦ null) ∗ Q }}

end spec

end AntHarness
end EtcdGrove
end Perennial
