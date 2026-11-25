/-
`putHeader(buf, kind, from, to, boot, seq)` (`udptransport.go`): `buf` with the datagram header
appended (`headerBytes`, `UdpWire.lean`).
(kvraft-udp, 2026-11-24: `notes/kvraft-udp-proof-plan.md`.)
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpWire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net Udp go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev putHeader.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (kind : w8) (src dst boot seq : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) }}
    (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putHeader)) (Val #buf)) (Val #kind)) (Val #src)) (Val #dst)) (Val #boot)) (Val #seq))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ headerBytes kind src dst boot seq) ∗
      ownSliceCap w8 s (DFrac.own 1) }}

end spec

end kvraft
end EtcdGrove
end Perennial
