/-
`u.ack(n, to, boot, seq)` (`nodeudp.go`): the ack of message `(boot, seq)` sent to replica `to`
(`putAck`, `write`: an ack is of the protocol, with no claim), counted in the node's stats.
(kvudp, 2026-11-24: `notes/kvudp-proof-plan.md`.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net Udp go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- See the file header. -/
abbrev udpNet.ack.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (u : Loc) (id boot : w64) (nd sp : Loc) (to b seq : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ isUdpNet F γu u id boot ∗ nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"stats"] ↦□ sp ∗ isStats sp }}
    (App (App (App (App (Val (u @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet.ty @!! go!"ack")) (Val #nd)) (Val #to)) (Val #b)) (Val #seq))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
