/-
`ValidAddrs(addrs, voters)` (addrs.go): `validAddrs l voters`: every address valid (`addrOk`) and
none twice, fewer than `2^32`, the bootstrap voters `1..voters` among them. (Each address shorter
than `2^63 - 1` bytes, as `AddrOk` needs.)
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
abbrev ValidAddrs.spec : Prop :=
  ∀ (addrs : GoSlice) (dq : DFrac) (l : List GoString) (voters : w64),
  (∀ a ∈ l, a.length + 1 < 2 ^ 63) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ addrs ↦*{dq} l }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ValidAddrs)) (Val #addrs)) (Val #voters))
  {{ RET #(validAddrs l (uint.nat voters)); addrs ↦*{dq} l }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
