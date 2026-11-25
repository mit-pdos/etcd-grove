/-
`parseAddr(a)` (`udptransport.go`): the IPv4 bytes and port of `a` and `true` if `AddrOk` accepts
it (`parseAddrM`, `UdpWire.lean`), else `false`.
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
abbrev parseAddr.spec : Prop :=
  ∀ (a : GoString), a.length + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.parseAddr)) (Val #a))
  {{ (ip : GoArray w8 4) (port : w64) (ok : Bool), RET (PairV (PairV #ip #port) #ok);
      ⌜ok = addrOk a ∧ (ok = true → parseAddrM a = some (ip.arr, port))⌝ }}

end spec

end kvraft
end EtcdGrove
end Perennial
