/-
`(*watchChan).ResultChan()` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:298-300`): the read-only
`resultChan` (k8s 7f-5b). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchCons

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev watchChan.ResultChan.spec : Prop :=
  ∀ (wc ch : Loc),
  {{ structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"resultChan" wc ↦□ ch }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"ResultChan")) (Val #()))
  {{ RET #ch; (True : IProp GF) }}

end spec

end k8s
end EtcdGrove
end Perennial
