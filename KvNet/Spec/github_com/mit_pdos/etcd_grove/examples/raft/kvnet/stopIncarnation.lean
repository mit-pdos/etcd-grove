/-
`stopIncarnation(r, t)` (`node.go`, 2026-11-24 G5): stops replica `r` (`Replica.stop`) and then its
transport (`ptStop`): from the incarnation's stopper, the start resource `S` again. Stated in the seams,
proved at the store's.
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
abbrev stopIncarnation.spec (stp : NodeStopper GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF) : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString),
  ⊢ stopLaw stp cfg M (S cfg.ID' cfg.Dir' cfg.Opts' M)

end spec

end raft_kvnet
end EtcdGrove
end Perennial
