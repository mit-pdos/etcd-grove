/-
`holdToken()` (`examples/k8s/compactor/compactor.go`, `notes/k8s-compactor-n-plan.md`; examples/k8s/etcd3's; cluster3's): sleeps forever.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

/-- `holdToken()` does not return (`False` after it): the goroutine `startCluster` runs it on holds
no resource and never ends, so `startCluster` keeps the token `wp_fork_tok_self` gives it, for the
member it serves next (cluster3's `holdToken.spec`). -/
abbrev holdToken.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.holdToken)) (Val #()))
  {{ RET #(); False }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
