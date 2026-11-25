/-
`putFragment(from, to, boot, seq, index, total, chunk)` (`udptransport.go`): a new slice holding
the fragment (`fragBytes`); `chunk` is only read.
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
abbrev putFragment.spec : Prop :=
  ∀ (src dst boot seq : w64) (index total : w32) (chunk : GoSlice) (q : DFrac) (cs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ chunk ↦*{q} cs }}
    (App (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putFragment)) (Val #src)) (Val #dst)) (Val #boot)) (Val #seq)) (Val #index)) (Val #total)) (Val #chunk))
  {{ (s : GoSlice), RET #s; s ↦* fragBytes src dst boot seq index total cs ∗
      ownSliceCap w8 s (DFrac.own 1) ∗ chunk ↦*{q} cs }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
