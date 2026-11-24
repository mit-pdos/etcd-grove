/-
`start(cfg, stats, newT)` (`node.go`, 2026-11-24 G5: `StartNode`'s body until then): an incarnation of
replica `cfg.ID` from its file and the start resource `S`, its transport made by `newT` (`ptCtor`):
the replica (its raft node, `rep`, `isNode`) and its stopper `stp`. Stated in the seams `rep`, `stp`
and `S`, as `StartNode.spec`; proved at the store's (`kvRep`, `kvNodeStart`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev start.spec (F : KvFacts GF) (AP : w64 → GoString → IProp GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF) (γ : Cluster) (N : Namespace) : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString),
  ⊢ startLaw F AP rep stp cfg M (S cfg.ID' cfg.Dir' cfg.Opts' M) γ N

end spec

end raft_kvnet
end EtcdGrove
end Perennial
