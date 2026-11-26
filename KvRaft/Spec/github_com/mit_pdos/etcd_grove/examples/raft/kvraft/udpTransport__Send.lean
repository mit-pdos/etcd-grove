/-
`t.Send(ms)` (`udptransport.go`): each message of `ms` handed to its peer's queue (a bag of
`qElem F pid`), or dropped (`dropped`) if no peer or a full queue. The caller gives the messages
away, each with its fact (`sendElem`, TCP's); the slice is only read.
(kvraft-udp, 2026-11-24: `notes/kvraft-udp-proof-plan.md`.)
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpDefs
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__Send

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
abbrev udpTransport.Send.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (msl : GoSlice) (dqs : DFrac) (ms : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isUdpCore F γu t γ N id n ∗ msl ↦*{dqs} ms ∗ [∗list] m ∈ ms, sendElem F m }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport.ty @!! go!"Send")) (Val #msl))
  {{ RET #(); msl ↦*{dqs} ms }}

end spec

end kvraft
end EtcdGrove
end Perennial
