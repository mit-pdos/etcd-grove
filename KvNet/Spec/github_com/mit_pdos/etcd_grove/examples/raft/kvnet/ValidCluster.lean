/-
`ValidCluster(addrs, voters, maxSizePerMsg, maxCommittedSizePerReady, maxInflightMsgs)`
(addrs.go): `validCluster`: `ValidAddrs`, raft's size limits not both 0, `MaxInflightMsgs` a positive
Go int below `2^62`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev ValidCluster.spec : Prop :=
  ∀ (addrs : GoSlice) (dq : DFrac) (l : List GoString) (voters msz mcs mif : w64),
  (∀ a ∈ l, a.length + 1 < 2 ^ 63) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ addrs ↦*{dq} l }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ValidCluster)) (Val #addrs)) (Val #voters)) (Val #msz))
      (Val #mcs)) (Val #mif))
  {{ RET #(validCluster l (uint.nat voters) (uint.nat msz) (uint.nat mcs) (uint.nat mif));
      addrs ↦*{dq} l }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
