/-
`bridgeAddr(i)` (`examples/k8s/etcd3/k8setcd3.go`, stage A of `notes/k8s-7f6-scope.md`): member `i`'s bridge address,
`127.0.0.1:(22000+i)` (`bridgeAt`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClusterN

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev bridgeAddr.spec : Prop :=
  ∀ (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.bridgeAddr)) (Val #i))
  {{ (s : GoString), RET #s; ⌜s = k8s_etcd3N.bridgeAt i⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
