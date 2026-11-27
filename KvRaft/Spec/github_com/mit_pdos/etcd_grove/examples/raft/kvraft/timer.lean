/-
`timer(d)` (`udptransport.go`): a channel that receives once, later (a bag of `struct{}`, no
fact: `sendSnapshot`'s select learns only that the time passed).
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
abbrev timer.spec : Prop :=
  ∀ (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.timer)) (Val #d))
  {{ (c : Loc), RET #c; ∃ γc : ChanNames, isChanBag (V := Unit) γc c (fun _ => iprop(True)) }}

end spec

end kvraft
end EtcdGrove
end Perennial
