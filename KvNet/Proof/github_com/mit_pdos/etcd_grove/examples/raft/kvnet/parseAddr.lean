/-
The proof of `KvNet/Spec/.../kvnet/parseAddr.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.parseAddr
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.AddrOk
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.decimal

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem parseAddr.wp_proof
    (wp_AddrOk : AddrOk.spec (GF := GF) (hG := hG))
    (wp_decimal : decimal.spec (GF := GF) (hG := hG)) :
    parseAddr.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end raft_kvnet
end EtcdGrove
end Perennial
