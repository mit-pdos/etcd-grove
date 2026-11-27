/-
`n.servePeer(c)` (`node.go`; `Transport.servePeer` before 2026-11-24 G5): reads a peer's frames
(after its hello byte) and steps each message addressed to this replica (`stepPeer`), until the
connection fails or a frame is bad.
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
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev Node.servePeer.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) : Prop :=
  ∀ (nd : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (c : GoInterface) (cn : Nat) (a : GoString) (eof ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isNodeS F rep stp nd γ N id ∗ net.isConn (GF := GF) c cn true a ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit ∗ recvTokL cn true (kvP F id) [helloPeerB] }}
    (App (Val (nd @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node.ty @!! go!"servePeer")) (Val #c))
  {{ RET #(); True }}

end spec

end kvraft
end EtcdGrove
end Perennial
