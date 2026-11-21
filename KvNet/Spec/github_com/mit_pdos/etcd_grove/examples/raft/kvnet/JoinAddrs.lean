/-
`JoinAddrs(addrs)` (addrs.go): the addresses joined by commas, `joinAddrs l`
(`splitAddrs_joinAddrs`: `SplitAddrs` reads them back when they are comma-free and at least one).
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
abbrev JoinAddrs.spec : Prop :=
  ∀ (addrs : GoSlice) (dq : DFrac) (l : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ addrs ↦*{dq} l }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.JoinAddrs)) (Val #addrs))
  {{ RET #(joinAddrs l); addrs ↦*{dq} l }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
