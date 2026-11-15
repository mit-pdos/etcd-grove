/-
`copyGetResponseMetadataOnly` (`util.go`): a fresh response with the cached one's header (copied),
`More` and `Count`, no key-values. Called on cached responses only (`leaseKey.get`). Changes: over
`cachedRespAt` (was `respOwn`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

def copyGetResponseMetadataOnly.spec : Prop :=
  ∀ (resp : Loc) (q : Qp) (m : RangeRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ cachedRespAt resp q m }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.copyGetResponseMetadataOnly)) (Val #resp))
  {{ (ret : Loc), RET #ret; cachedRespAt resp q m ∗ rangeRespOwn ret (DFrac.own 1) { m with kvs := [] } }}

end spec

end Leasing
end EtcdGrove
end Perennial
