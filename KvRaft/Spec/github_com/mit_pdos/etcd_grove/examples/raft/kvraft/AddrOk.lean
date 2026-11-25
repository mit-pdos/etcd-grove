/-
`AddrOk(a)` (addrs.go): exactly the net extension's `addrOk a` (`GooseLang/Ext/Net/Impl.lean`)
(`goAddrOk_eq`), for every string: one longer than 21 bytes is refused before the loops (whose
index, run up to `len(a)` inclusive, would wrap past `len(a) = 2^63 - 1`).
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
abbrev AddrOk.spec : Prop :=
  ∀ (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.AddrOk)) (Val #a))
  {{ RET #(Net.addrOk a); True }}

end spec

end kvraft
end EtcdGrove
end Perennial
