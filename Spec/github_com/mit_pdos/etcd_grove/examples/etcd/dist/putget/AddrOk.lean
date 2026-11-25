/-
`AddrOk(a)` (`examples/etcd/dist/putget/putget.go`, a copy of `examples/raft/kvnet/addrs.go`'s): exactly the net extension's `addrOk a` (`GooseLang/Ext/Net/Impl.lean`), the
check `Member` and `Client` run on their addresses (`goAddrOk_eq`). For `a` shorter than `2^63 - 1`
bytes: its first loop runs `i` up to `len(a)` inclusive, and `i + 1` past `len(a) = 2^63 - 1` would
wrap (a string no Go program can hold).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI putget_addr

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]

/-- See the file header. -/
abbrev AddrOk.spec : Prop :=
  ∀ (a : GoString), a.length + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AddrOk)) (Val #a))
  {{ RET #(Net.addrOk a); True }}

end spec

end etcd_putget_dist
end EtcdGrove
end Perennial
