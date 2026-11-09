/-
`clientv3.WithZapLogger` (`client/v3/client.go`).

Users: `v3client.New`.

Proof sketch: a closure storing the logger into the client's atomic pointer (`clientOptAt`).

Changes: new (round 1).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `WithZapLogger(lg)`: an option storing a logger. -/
def WithZapLogger.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ Zap.isLogger lg }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithZapLogger)) (Val #lg))
  {{ (f : GoFunc), RET #f; clientOptAt f }}

end spec

end ClientV3
end EtcdGrove
end Perennial
