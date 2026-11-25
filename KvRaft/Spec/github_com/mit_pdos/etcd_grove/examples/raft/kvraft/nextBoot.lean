/-
`nextBoot(dir, id)` (`nodeudp.go`): the process's boot number `boot`, one more than the file's,
written durably before it is returned (`durable.Read`, `durable.Write`), with the process's ghost
counter at it, fresh (`udpCtr γu id boot 0`): the boot file invariant (`UdpBootDefs.lean`) bumps
`udpHi` at the write's sync, in the names' invariant. Never the panic (the invariant has the file
this package's: `bootVal`); it never returns at the largest counter (partial correctness).
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
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

/-- See the file header. -/
abbrev nextBoot.spec : Prop :=
  ∀ (γu : UdpNames) (id : w64) (dir : GoString) (bn : UdpBootNames) (qc : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ udpMsgInv γu ∗ udpBootStart γu id dir bn qc }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.nextBoot)) (Val #dir)) (Val #id))
  {{ (boot : w64), RET #boot; udpCtr γu id boot (W64 0) ∗ udpBootStart γu id dir bn qc }}

end spec

end kvraft
end EtcdGrove
end Perennial
