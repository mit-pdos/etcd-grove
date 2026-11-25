/-
`startNode(cfg, newT)` (`node.go`, 2026-11-24 G5): the node of replica `cfg.ID`, its first incarnation
started (`start`, by `startLaw` at the resource `R`) with transports made by `newT`: `isNodeS`, which
keeps the restart's laws at `R`. `StartNode` is it at TCP's constructor.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.NodeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev startNode.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.NodeConfig) (M : GMap w64 GoString) (f : GoFunc) (γ : Cluster) (N : Namespace)
    (AP : w64 → GoString → IProp GF) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ cfg.Addrs' ↦$□ M ∗ R ∗ ptCtor F γ N cfg.ID' AP f ∗ stepLaw F γ N cfg.ID' ∗
      ⌜Cluster.trace γ = none⌝ ∗ stopLaw stp cfg M R ∗ startLaw F AP rep stp cfg M R γ N }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.startNode)) (Val #cfg)) (Val #f))
  {{ (nd : Loc), RET #nd; isNodeS F rep stp nd γ N cfg.ID' }}

end spec

end kvraft
end EtcdGrove
end Perennial
