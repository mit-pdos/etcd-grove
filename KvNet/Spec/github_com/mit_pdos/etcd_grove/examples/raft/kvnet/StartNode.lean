/-
`StartNode(cfg)` (`examples/raft/kvnet/node.go`): an incarnation of the replica `cfg.ID` started from
its durable file: a node `nd` (`isNodeS`, over the store's seam `rep`) with its conf law. **A spec at
the store's seam**: `S id dir opts M` is what the start takes, at the configuration's id, directory, options
and address map `M` (read-only, `cfg.Addrs`): the file's and raft's start resources, every other replica's
address protocol, fixed by the store layer with the crash law (decision A; ledger 2026-11-22, kvnet's
`StartNode`: indexed by the configuration). `Run`'s proof takes it as a callee.
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
abbrev StartNode.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF) : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      cfg.Addrs' ↦$□ M ∗ S cfg.ID' cfg.Dir' cfg.Opts' M }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartNode)) (Val #cfg))
  {{ (nd : Loc), RET #nd; ∃ (γ : Cluster) (N : Namespace) (n : NodeH),
      isNodeS F rep nd γ N cfg.ID' n ∗ confLaw F rep cf γ N cfg.ID' }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
