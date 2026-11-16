/-
`holdToken()` (`examples/etcd/txnlinfaultsN/txnlinfaultsN.go`; cluster3's): sleeps forever.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Base

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

/-- `holdToken()` does not return (`False` after it): the goroutine `startCluster` runs it on holds
no resource and never ends, so `startCluster` keeps the token `wp_fork_tok_self` gives it, for the
member it serves next (cluster3's `holdToken.spec`). -/
abbrev holdToken.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.holdToken)) (Val #()))
  {{ RET #(); False }}

end spec

end etcd_txnlinfaultsN
end EtcdGrove
end Perennial
