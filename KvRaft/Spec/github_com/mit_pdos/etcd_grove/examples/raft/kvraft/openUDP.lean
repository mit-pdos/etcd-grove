/-
`openUDP(cfg)` (`nodeudp.go`): the process's endpoint (`isUdpNet`): every address of `cfg.Addrs`
parsed (`udpAddr`), its own bound (`listenUDP`), the boot number taken (`nextBoot`). Its own address
is valid (`M !! cfg.ID = some a`, every address valid: `RunNodeUDP`'s `ValidCluster`), so the
panic cannot happen.
(kvraft-udp, 2026-11-24: `notes/kvraft-udp-proof-plan.md`.)
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpBootDefs

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
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

/-- See the file header. -/
abbrev openUDP.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.NodeConfig) (M : GMap w64 GoString) (a : GoString),
  M !! cfg.ID' = some a →
  (∀ pid a', M !! pid = some a' → addrOk a' = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ cfg.Addrs' ↦$□ M ∗ udpProcStart F γu cfg.ID' cfg.Dir' M }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.openUDP)) (Val #cfg))
  {{ (u : Loc), RET #u; ∃ boot, isUdpNet F γu u cfg.ID' boot }}

end spec

end kvraft
end EtcdGrove
end Perennial
