/-
`u.acked(from, seq)` (`udptransport.go`): the waiter of `seq` for `from`, if any, woken (its
channel closed with the closer the map held) and removed. Acks carry no claim.
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
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- See the file header. -/
abbrev udpNet.acked.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (u : Loc) (id boot : w64) (src seq : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isUdpNet F γu u id boot }}
    (App (App (Val (u @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet.ty @!! go!"acked")) (Val #src)) (Val #seq))
  {{ (b : Bool), RET #b; True }}

end spec

end kvraft
end EtcdGrove
end Perennial
