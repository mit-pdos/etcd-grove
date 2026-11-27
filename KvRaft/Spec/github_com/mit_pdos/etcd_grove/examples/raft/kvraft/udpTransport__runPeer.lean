/-
`t.runPeer(p)` (`udptransport.go`): the peer `p`'s sender: each message it receives from its
queue (`qElem F pid`: the message with its fact) gets a fresh name (`nextSeq`'s token), which it
records with the message's encoding (`udpMsgAt`, from the token in the names' invariant), so its
fragments (`fragments`) are of the protocol; a snapshot is handed to `sendSnapshot`, any other
message written (`writeAll`), or dropped (`dropped`). It returns when the transport stops.
(kvraft-udp, 2026-11-24: `notes/kvraft-udp-proof-plan.md`.)
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net Udp go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]

/-- See the file header. -/
abbrev udpTransport.runPeer.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (p : Loc) (pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isUdpCore F γu t γ N id n ∗ isUdpPeer F p pid }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport.ty @!! go!"runPeer")) (Val #p))
  {{ RET #(); True }}

end spec

end kvraft
end EtcdGrove
end Perennial
