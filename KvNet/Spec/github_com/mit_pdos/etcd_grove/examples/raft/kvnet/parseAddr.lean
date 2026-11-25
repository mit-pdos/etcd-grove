/-
`parseAddr(a)` (`udptransport.go`): the IPv4 bytes and port of `a` and `true` if `AddrOk` accepts
it (`parseAddrM`, `UdpWire.lean`), else `false`.
(kvudp, 2026-11-24: `notes/kvudp-proof-plan.md`.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpWire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net Udp go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev parseAddr.spec : Prop :=
  ∀ (a : GoString), a.length + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.parseAddr)) (Val #a))
  {{ (ip : GoArray w8 4) (port : w64) (ok : Bool), RET (PairV (PairV #ip #port) #ok);
      ⌜ok = addrOk a ∧ (ok = true → parseAddrM a = some (ip.arr, port))⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
