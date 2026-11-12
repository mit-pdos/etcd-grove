/-
`inRange` (`cache.go`): `begin ≤ k`, and `k < end` unless `end = "\x00"` (`strings.Compare`,
Perennial's). Changes: `inRangeM` (was `leaseInRange`).
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

def inRange.spec : Prop :=
  ∀ (k b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.inRange)) (Val #k)) (Val #b)) (Val #e))
  {{ RET #(inRangeM k b e); True }}

end spec

end Leasing
end EtcdGrove
end Perennial
