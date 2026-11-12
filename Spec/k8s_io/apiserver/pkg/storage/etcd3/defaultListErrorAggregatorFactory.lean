/-
`defaultListErrorAggregatorFactory()` (`store.go`): a new aggregator, fresh (`freshAggr`: its `Aggregate()` returns `nil`; k8s etcd3 7e-2, D2). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.AggrDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev defaultListErrorAggregatorFactory.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.defaultListErrorAggregatorFactory)) (Val #()))
  {{ (e : GoInterface), RET #e; freshAggr e }}

end spec

end k8s
end EtcdGrove
end Perennial
