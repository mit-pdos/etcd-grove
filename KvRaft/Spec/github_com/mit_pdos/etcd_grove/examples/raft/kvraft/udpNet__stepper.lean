/-
`u.stepper(n, q)` (`nodeudp.go`): steps each message of `q` (a bag of `recvElem F id`: what
`Node.stepPeer` takes) on the current incarnation, acknowledging each snapshot (`ack`). Forever.
(kvraft-udp, 2026-11-24: `notes/kvraft-udp-proof-plan.md`.)
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpDefs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.NodeDefs

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
abbrev udpNet.stepper.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) : Prop :=
  ∀ (γu : UdpNames) (u : Loc) (id boot : w64) (nd : Loc) (γ : Cluster) (N : Namespace) (q : Loc) (γq : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isUdpNet F γu u id boot ∗ isNodeS F rep stp nd γ N id ∗ context.isClosedchanInit ∗
      isChanBag (V := github_com.mit_pdos.etcd_grove.examples.raft.kvraft.received) γq q (recvElem F id) }}
    (App (App (Val (u @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet.ty @!! go!"stepper")) (Val #nd)) (Val #q))
  {{ RET #(); True }}

end spec

end kvraft
end EtcdGrove
end Perennial
