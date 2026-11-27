/-
`t.writeAll(to, ds)` (`udptransport.go`): the datagrams `ds` (read-only, each of the protocol:
`udpDgsOk`) written to replica `to` in order (`udpNet.write`), until one fails; the result says
whether all were. The slice is only read.
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
abbrev udpTransport.writeAll.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (t : Loc) (id : w64) (sc : Loc) (γsc : ChanNames) (to : w64)
    (dsl : GoSlice) (q : DFrac) (ds : List GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isUdpBase F γu t id sc γsc ∗ dsl ↦*{q} ds ∗ udpDgsOk F γu ds }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport.ty @!! go!"writeAll")) (Val #to)) (Val #dsl))
  {{ (ok : Bool), RET #ok; dsl ↦*{q} ds }}

end spec

end kvraft
end EtcdGrove
end Perennial
