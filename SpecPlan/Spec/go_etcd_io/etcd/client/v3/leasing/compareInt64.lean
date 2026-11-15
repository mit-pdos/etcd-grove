/-
`compareInt64` (`util.go`): `-1`, `0`, `1`. Changes: unchanged (mirrors the code).
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

def compareInt64.spec : Prop :=
  ∀ (a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.compareInt64)) (Val #a)) (Val #b))
  {{ RET #(W64 (cmpInt (sint.Z a) (sint.Z b))); True }}

end spec

end Leasing
end EtcdGrove
end Perennial
