/-
`AddrOk(a)` (addrs.go): exactly the net extension's `addrOk a` (`GooseLang/Ext/Net/Impl.lean`), the
top-level theorem's premise on a replica address (`goAddrOk_eq`). For `a` shorter than `2^63 - 1`
bytes: its first loop runs `i` up to `len(a)` inclusive, and `i + 1` past `len(a) = 2^63 - 1` would
wrap (a string no Go program can hold).
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
abbrev AddrOk.spec : Prop :=
  ∀ (a : GoString), a.length + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.AddrOk)) (Val #a))
  {{ RET #(Net.addrOk a); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
