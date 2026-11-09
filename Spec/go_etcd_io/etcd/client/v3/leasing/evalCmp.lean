/-
`evalCmp` (`util.go`): a comparison on a cached response (`evalCmpM`: not etcd's,
`issues/leasing-evalcmp-missing-key.md`). Proof sketch: `GetCompare`, the getters (W0, 3h);
`bytes.Compare`, `compareInt64`. Changes: over `cachedRespAt`, W0's `cmpAt` (was `respOwn`, `CmpModel`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

/-- `evalCmp(resp, cmp)`. -/
def evalCmp.spec : Prop :=
  ∀ (resp : Loc) (q : Qp) (m : RangeRespM) (c : go_etcd_io.etcd.client.v3.Cmp)
    (mc : Option EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ cachedRespAt resp q m ∗ cmpAt c mc }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.evalCmp)) (Val #resp)) (Val #c))
  {{ RET #(evalCmpM m (mc.getD Compare.zero)); cachedRespAt resp q m }}

end spec

end Leasing
end EtcdGrove
end Perennial
