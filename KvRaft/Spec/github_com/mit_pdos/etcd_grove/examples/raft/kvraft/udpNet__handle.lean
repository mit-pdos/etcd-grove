/-
`u.handle(n, r, steps, b)` (`nodeudp.go`): the datagram `b`, of the protocol (`udpDgOk`, as
`receive` read it): an ack wakes its waiter (`acked`); a fragment goes to the reassembler (`add`,
with its fact), and a message it completes, decoded (`getMsg`, from the recorded body's fact) and
addressed to this replica, is queued to its sender's stepper (`steps`: a bag of `recvElem F id`
per peer) or dropped. `b` is only read.
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
abbrev udpNet.handle.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (u : Loc) (id boot : w64) (nd sp r stm : Loc) (Q : GMap w64 Loc) (b : GoSlice) (q : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isUdpNet F γu u id boot ∗ nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node, go!"stats"] ↦□ sp ∗ isStats sp ∗ ownReassembler F γu r ∗
      stm ↦$□ Q ∗ ([∗map] _pid ↦ c ∈ Q, ∃ γq : ChanNames,
        isChanBag (V := github_com.mit_pdos.etcd_grove.examples.raft.kvraft.received) γq c (recvElem F id)) ∗
      b ↦*{q} bs ∗ udpDgOk F γu bs }}
    (App (App (App (App (Val (u @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet.ty @!! go!"handle")) (Val #nd)) (Val #r)) (Val #stm)) (Val #b))
  {{ RET #(); ownReassembler F γu r ∗ b ↦*{q} bs }}

end spec

end kvraft
end EtcdGrove
end Perennial
