/-
`ValidAddrs(addrs, voters)` (addrs.go): `validAddrs l voters`: every address valid (`addrOk`) and
none twice, fewer than `2^32`, the bootstrap voters `1..voters` among them.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev ValidAddrs.spec : Prop :=
  ∀ (addrs : GoSlice) (dq : DFrac) (l : List GoString) (voters : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ addrs ↦*{dq} l }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.ValidAddrs)) (Val #addrs)) (Val #voters))
  {{ RET #(validAddrs l (uint.nat voters)); addrs ↦*{dq} l }}

end spec

end kvraft
end EtcdGrove
end Perennial
