/-
`u.write(to, b)` (`udptransport.go`): `b`, a datagram of the protocol (`udpDgOk`, so at most
`maxDatagram` bytes: it arrives intact), sent to replica `to`'s address if the endpoint has one
(`WriteToUDP`, whose atomic update adds it to the address's invariant with its fact); the result
says whether it was sent. `b` is read-only.
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
abbrev udpNet.write.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (u : Loc) (id boot : w64) (to : w64) (b : GoSlice) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isUdpNet F γu u id boot ∗ b ↦*□ bs ∗ udpDgOk F γu bs }}
    (App (App (Val (u @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet.ty @!! go!"write")) (Val #to)) (Val #b))
  {{ (ok : Bool), RET #ok; True }}

end spec

end kvraft
end EtcdGrove
end Perennial
