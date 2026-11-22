/-
`t.runPeer(p)` (`examples/raft/kvnet/transport.go`): the peer `p`'s sender: it receives the queued
messages (`p.queue`, a bag of `qElem F pid`) and writes each one as a frame (`putMsg`, `writeFrame`)
to a connection to the peer's address (dialed by `dial` when it has none), within `closeAfter`'s
deadline; a message it cannot send is dropped (`dropped`) and the connection closed. What it writes
on a connection is the peer stream of the address's protocol (`kvP F pid`: the hello byte, then whole
frames of messages with their facts, `peer_send`). The queue is never closed: it never returns
(partial correctness).
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

/-- See the file header. -/
abbrev Transport.runPeer.spec : Prop :=
  ∀ (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (p : Loc)
    (pid : w64) (a : GoString) (et ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      isTransportCore F t γ N id n ∗ isPeer F p pid a ∗ globalAddr net.errTimeout ↦□ et ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport.ty
      @!! go!"runPeer")) (Val #p))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
