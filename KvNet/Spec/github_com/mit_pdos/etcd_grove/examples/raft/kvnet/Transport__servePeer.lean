/-
`t.servePeer(c)` (`examples/raft/kvnet/transport.go`): the replica `id` serves a peer's connection
`c` (its accepted end, `cn`, `true`), whose hello byte it has read (`recvTokL cn true (kvP F id)
[helloPeerB]`, the reader's token of the protocol `kvP`, `Proto.lean`): frames, each read back as a
message (`getMsg`) and, if addressed to `id`, stepped on the node (`node.Step`, by the step law:
`isTransportCore`'s seam), until the connection fails, ends, or carries a frame not for `id`; then
`c` is closed (`connIs cn`: a library connection). Partial correctness: it returns, with nothing.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TransportDefs

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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev Transport.servePeer.spec : Prop :=
  ∀ (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH)
    (c : GoInterface) (cn : Nat) (a : GoString) (eof ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      isTransportCore F t γ N id n ∗ net.isConn (GF := GF) c cn true a ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit ∗ recvTokL cn true (kvP F id) [helloPeerB] }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport.ty
      @!! go!"servePeer")) (Val #c))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
