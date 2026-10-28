/-
`parseRVForMetricsWithTruncation(rv)` (`thread_safe_store.go:546`): the resource version's last 15
digits as an integer, for the store's metric. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `parseRVForMetricsWithTruncation(rv)`: some integer and error (only the metric uses them). -/
abbrev parseRVForMetricsWithTruncation.spec : Prop :=
  ∀ (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache }}
    (App (Val (@! parseRVForMetricsWithTruncation)) (Val #rv))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); True }}

end spec

end cache
end EtcdGrove
end Perennial
