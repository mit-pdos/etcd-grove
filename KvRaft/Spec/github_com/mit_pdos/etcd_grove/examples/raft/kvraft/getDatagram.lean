/-
`getDatagram(b)` (`udptransport.go`): `b` read back (`parseDg`, `UdpWire.lean`): the datagram
(`dgOwn`: its fields, its chunk a new slice) and `true`, or `false` for anything `putFragment`
or `putAck` did not write. `b` is only read.
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
abbrev getDatagram.spec : Prop :=
  ∀ (b : GoSlice) (q : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ b ↦*{q} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getDatagram)) (Val #b))
  {{ (d : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.datagram) (ok : Bool), RET (PairV #d #ok); b ↦*{q} bs ∗
      match parseDg bs with
      | some dg => ⌜ok = true⌝ ∗ dgOwn (GF := GF) d dg
      | none => ⌜ok = false⌝ }}

end spec

end kvraft
end EtcdGrove
end Perennial
