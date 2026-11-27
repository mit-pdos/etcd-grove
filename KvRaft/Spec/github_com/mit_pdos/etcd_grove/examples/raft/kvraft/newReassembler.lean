/-
`newReassembler(stats)` (`udptransport.go`): an empty reassembler (`ownReassembler`).
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
abbrev newReassembler.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (sts : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isStats sts }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.newReassembler)) (Val #sts))
  {{ (r : Loc), RET #r; ownReassembler F γu r }}

end spec

end kvraft
end EtcdGrove
end Perennial
