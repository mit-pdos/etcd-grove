/-
`bridgeAddr(i)` (`examples/etcd/txnlinfaultsN/txnlinfaultsN.go`): member `i`'s bridge address,
`127.0.0.1:(28000+i)` (`bridgeAt`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlinfaultsN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]

/-- See the file header. -/
abbrev bridgeAddr.spec : Prop :=
  ∀ (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.bridgeAddr)) (Val #i))
  {{ (s : GoString), RET #s; ⌜s = bridgeAt i⌝ }}

end spec

end etcd_txnlinfaultsN
end EtcdGrove
end Perennial
