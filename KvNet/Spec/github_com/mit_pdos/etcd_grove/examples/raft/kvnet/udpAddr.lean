/-
`udpAddr(a)` (`udptransport.go`): for `a` that `AddrOk` accepts, a new `*UDPAddr` (read-only
for good, `udpAddrAt`) whose IP and port make `a` (`ValidDest`: what `WriteToUDP` and `ListenUDP`
take) and `true`; `false` otherwise.
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
abbrev udpAddr.spec : Prop :=
  ∀ (a : GoString), a.length + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpAddr)) (Val #a))
  {{ (p : Loc) (ok : Bool), RET (PairV #p #ok); ⌜ok = addrOk a⌝ ∗
      (⌜ok = false⌝ ∨ ∃ (ip : List w8) (port : w64), net.udpAddrAt (GF := GF) p ip port ∗
        ⌜ValidDest ip port a⌝) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
